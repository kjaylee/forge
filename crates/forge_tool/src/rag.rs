use std::sync::Arc;
use std::path::PathBuf;
use forge_domain::{Description, ToolCallService};
use forge_domain::{SymbolQuery, CodeContext, RelationshipKind};
use forge_rag::service::{CodeContextService, CodeContextServiceImpl};
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::debug;

#[derive(Deserialize, JsonSchema)]
pub struct RAGInput {
    /// Symbol search/analysis query
    pub query: SymbolQuery,
    /// Path to the workspace to analyze
    pub workspace_root: PathBuf,
}

#[derive(Serialize, JsonSchema, Debug)]
pub struct RAGOutput {
    /// Located code symbols and their relationships
    pub context: CodeContext,
}

/// Query code understanding using IDE-like capabilities through Language Server Protocol.
///
/// Features:
/// 1. Symbol Navigation - Find definitions, references, and implementations
/// 2. Relationship Discovery - Analyze code dependencies and connections
/// 3. Smart Context - Understand code structure and relationships
/// 4. Cross-file Analysis - Navigate and understand cross-file relationships
/// 5. Structured Understanding - Get typed information about code elements
///
/// Example query to find a class and its relationships:
/// ```json
/// {
///   "query": {
///     "Name": "UserManager"
///   },
///   "workspace_root": "/path/to/code"
/// }
/// ```

#[derive(Description)]
pub struct RAG {
    service: Arc<RwLock<dyn CodeContextService>>,
}

impl RAG {
    pub async fn with_workspace(workspace_root: PathBuf) -> Result<Self, String> {
        // Create service
        let mut service = CodeContextServiceImpl::with_workspace(workspace_root.clone());
        
        // Initialize workspace
        service.initialize_workspace(&workspace_root).await
            .map_err(|e| format!("Failed to initialize workspace: {}", e.0))?;
        
        Ok(Self { 
            service: Arc::new(RwLock::new(service))
        })
    }
}

#[async_trait::async_trait]
impl ToolCallService for RAG {
    type Input = RAGInput; 
    type Output = RAGOutput;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        debug!("RAG call - query: {:?}, workspace: {:?}", input.query, input.workspace_root);
        
        let mut service = self.service.write().await;
        
        // Only initialize if workspace path changed
        let current_root = service.get_workspace_root();
        debug!("Current workspace root: {:?}", current_root);
        debug!("Input workspace root: {:?}", input.workspace_root);
        if current_root != &input.workspace_root {
            debug!("Workspace changed, initializing new workspace");
            service.initialize_workspace(&input.workspace_root).await
                .map_err(|e| format!("Failed to initialize workspace: {}", e.0))?;
        }

        debug!("Getting symbols");
        let symbols = service
            .get_symbol_context(&input.query).await
            .map_err(|e| format!("Failed to get symbols: {}", e.0))?;
        debug!("Found {} symbols", symbols.len());

        let mut relationships = Vec::new();
        for symbol in &symbols {
            debug!("Analyzing relationships for symbol: {:?}", symbol.id);
            let symbol_rels = service
                .analyze_relationships(symbol.id.clone()).await
                .map_err(|e| format!("Failed to analyze relationships: {}", e.0))?;
            debug!("Found {} relationships", symbol_rels.len());
            relationships.extend(symbol_rels);
        }

        Ok(RAGOutput {
            context: CodeContext {
                symbols,
                relationships,
                workspace_root: input.workspace_root,
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;
    use std::fs;
    use forge_domain::SymbolKind;
    use tracing_test::traced_test;

    async fn setup_test_files(dir: &TempDir) -> std::path::PathBuf {
        // Create src directory
        let src_dir = dir.path().join("src");
        fs::create_dir_all(&src_dir).unwrap();

        // Create simple test file with exact positions for LSP
        let test_src = r#"// Test file for symbol detection
struct User {
    id: i32,
    name: String,
}

impl User {
    fn new(id: i32, name: String) -> Self {
        Self { id, name }
    }

    fn get_id(&self) -> i32 {
        self.id
    }
}

fn main() {
    let user = User::new(1, "test".to_string());
    println!("User id: {}", user.get_id());
}"#;

        debug!("Test source content before writing:\n{}", test_src);

        // Write with Unix line endings for consistency in position detection
        let test_file = src_dir.join("main.rs");
        fs::write(&test_file, &test_src).unwrap();

        // Verify file was written correctly
        let content = fs::read_to_string(&test_file).unwrap();
        debug!("Verifying file content:\n{}", content);
        assert_eq!(content, test_src, "File content does not match expected");

        debug!("Created test file at: {:?}", test_file);
        debug!("Test file content:\n{}", test_src);

        // Initialize workspace
        let workspace_path = dir.path().to_path_buf();
        debug!("Using workspace path: {:?}", workspace_path);
        workspace_path
    }

    #[tokio::test]
    #[traced_test]
    async fn test_basic_symbol_detection() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_path = setup_test_files(&temp_dir).await;

        // Create and initialize RAG instance
        let rag = RAG::with_workspace(workspace_path.clone()).await.unwrap();

        // Test struct detection
        let result = rag
            .call(RAGInput {
                query: SymbolQuery::Name("User".to_string()),
                workspace_root: workspace_path.clone(),
            })
            .await
            .unwrap();

        debug!("Struct detection result: {:?}", result);
        assert!(!result.context.symbols.is_empty(), "No symbols found");
        let struct_symbol = result.context.symbols.iter().find(|s| s.kind == SymbolKind::Struct);
        assert!(struct_symbol.is_some(), "User struct not found");
        assert_eq!(struct_symbol.unwrap().name, "User");

        // Test method detection
        let result = rag
            .call(RAGInput {
                query: SymbolQuery::Name("new".to_string()),
                workspace_root: workspace_path,
            })
            .await
            .unwrap();

        debug!("Method detection result: {:?}", result);
        assert!(!result.context.symbols.is_empty(), "No symbols found");
        let method_symbol = result.context.symbols.iter().find(|s| s.kind == SymbolKind::Method);
        assert!(method_symbol.is_some(), "new method not found");
        assert_eq!(method_symbol.unwrap().name, "new");
    }

    #[tokio::test]
    #[traced_test]
    async fn test_find_relationships() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_path = setup_test_files(&temp_dir).await;

        // Create and initialize service
        let service = Arc::new(RwLock::new(CodeContextServiceImpl::with_workspace(
            workspace_path.clone(),
        )));

        // Initialize workspace and verify symbols
        let mut svc = service.write().await;
        svc.initialize_workspace(&workspace_path).await.unwrap();
        let symbols = svc
            .get_symbol_context(&SymbolQuery::Name("new".to_string()))
            .await
            .unwrap();
        assert!(!symbols.is_empty(), "Failed to find 'new' method in test setup");
        drop(svc);

        // Create RAG with initialized service
        let rag = RAG { service };

        // Test finding relationships
        let result = rag
            .call(RAGInput {
                query: SymbolQuery::Name("new".to_string()),
                workspace_root: workspace_path,
            })
            .await
            .unwrap();

        debug!(
            "Test result - symbols: {:?}, relationships: {:?}",
            result.context.symbols, result.context.relationships
        );

        assert!(!result.context.symbols.is_empty(), "No symbols found");
        assert!(!result.context.relationships.is_empty(), "No relationships found");
        let has_struct_relation = result
            .context
            .relationships
            .iter()
            .any(|r| r.kind == RelationshipKind::Contains);
        assert!(
            has_struct_relation,
            "Expected Contains relationship between User::new and User"
        );
    }

    #[tokio::test]
    #[traced_test]
    async fn test_no_matches() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_path = setup_test_files(&temp_dir).await;

        // Create and initialize service with workspace
        let service = Arc::new(RwLock::new(CodeContextServiceImpl::with_workspace(
            workspace_path.clone(),
        )));

        let mut svc = service.write().await;
        svc.initialize_workspace(&workspace_path).await.unwrap();
        drop(svc);

        // Create RAG with initialized service
        let rag = RAG { service };

        // Test non-existent symbol
        let result = rag
            .call(RAGInput {
                query: SymbolQuery::Name("NonExistent".to_string()),
                workspace_root: workspace_path,
            })
            .await
            .unwrap();

        debug!(
            "Test result - symbols: {:?}, relationships: {:?}",
            result.context.symbols, result.context.relationships
        );

        assert!(result.context.symbols.is_empty(), "Expected no symbols");
        assert!(
            result.context.relationships.is_empty(),
            "Expected no relationships"
        );
    }
}
