pub mod analysis;
pub mod cache;
pub mod language;
pub mod lsp;
pub mod service;

use std::{path::PathBuf, sync::Arc};
use tokio::sync::RwLock;

use cache::{SymbolStore, SymbolCache};
pub use forge_domain::{Symbol, SymbolId, SymbolQuery, SymbolRelationship, Location, SymbolKind};
use lsp::LSPManager;
use service::{CodeContextService, CodeContextServiceImpl};
use analysis::RelationshipAnalyzer;

pub struct RagManager {
    code_context_service: Arc<RwLock<dyn CodeContextService>>,
    workspace_root: PathBuf,
}

impl RagManager {
    pub fn new(workspace_root: PathBuf, symbol_store: Arc<dyn SymbolStore>) -> Self {
        let lsp_manager = Arc::new(LSPManager::new(workspace_root.clone()));
        let relationship_analyzer = Arc::new(RwLock::new(RelationshipAnalyzer::new()));
        let symbol_cache = Arc::new(SymbolCache::new(1000, symbol_store));

        let service = CodeContextServiceImpl::new(
            lsp_manager,
            relationship_analyzer,
            symbol_cache,
            workspace_root.clone(),
        );

        Self {
            code_context_service: Arc::new(RwLock::new(service)),
            workspace_root,
        }
    }

    pub async fn get_symbol(&self, symbol_id: &SymbolId) -> Option<Symbol> {
        match self.code_context_service.read().await
            .get_symbol_context(&SymbolQuery::Id(symbol_id.clone())).await {
            Ok(mut symbols) if !symbols.is_empty() => Some(symbols.remove(0)),
            _ => None,
        }
    }

    pub async fn analyze_symbol_relationships(&self, symbol_id: &SymbolId) -> Result<String, &'static str> {
        match self.code_context_service.read().await
            .analyze_relationships(symbol_id.clone()).await {
            Ok(relationships) => {
                let mut result = String::new();
                for relationship in relationships {
                    result.push_str(&format!("{} {} {}\n", 
                        relationship.from.0,
                        relationship.kind.to_string(),
                        relationship.to.0
                    ));
                }
                Ok(result)
            }
            Err(_) => Err("Failed to analyze relationships"),
        }
    }

    pub async fn initialize_workspace(&self) -> Result<(), &'static str> {
        self.code_context_service.write().await
            .initialize_workspace(&self.workspace_root)
            .await
            .map_err(|_| "Failed to initialize workspace")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;
    use cache::InMemorySymbolStore;

    #[tokio::test]
    async fn test_rag_manager_creation() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let store = Arc::new(InMemorySymbolStore::new());
        
        let manager = RagManager::new(workspace_root.clone(), store);
        assert_eq!(manager.workspace_root, workspace_root);
    }

    #[tokio::test]
    async fn test_index_workspace() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let store = Arc::new(InMemorySymbolStore::new());
        
        let manager = RagManager::new(workspace_root.clone(), store);
        let result = manager.initialize_workspace().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_get_symbol() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let store = Arc::new(InMemorySymbolStore::new());
        
        let manager = RagManager::new(workspace_root.clone(), store);
        let _ = manager.initialize_workspace().await;
        
        // Test getting User struct
        let symbol = manager.get_symbol(&SymbolId("User".to_string())).await;
        assert!(symbol.is_some());
        let user = symbol.unwrap();
        assert_eq!(user.name, "User");
        assert_eq!(user.kind, SymbolKind::Struct);

        // Test getting User::new method
        let symbol = manager.get_symbol(&SymbolId("User::new".to_string())).await;
        assert!(symbol.is_some());
        let new_method = symbol.unwrap();
        assert_eq!(new_method.name, "new");
        assert_eq!(new_method.kind, SymbolKind::Method);
    }

    #[tokio::test]
    async fn test_analyze_relationships() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let store = Arc::new(InMemorySymbolStore::new());
        
        let manager = RagManager::new(workspace_root.clone(), store);
        let _ = manager.initialize_workspace().await;

        // Test User::new relationships
        let result = manager.analyze_symbol_relationships(&SymbolId("User::new".to_string())).await;
        assert!(result.is_ok());
        let relationships = result.unwrap();
        assert!(!relationships.is_empty());
        assert!(relationships.contains("User::new contains User"));

        // Test User relationships
        let result = manager.analyze_symbol_relationships(&SymbolId("User".to_string())).await;
        assert!(result.is_ok());
        let relationships = result.unwrap();
        assert!(!relationships.is_empty());
        assert!(relationships.contains("User contains User::new"));
    }
}
