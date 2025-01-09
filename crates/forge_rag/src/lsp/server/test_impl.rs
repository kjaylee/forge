use std::path::PathBuf;
use forge_domain::{Symbol, SymbolId, SymbolKind, Location};
use tokio::sync::RwLock;
use tracing::debug;
use std::sync::Arc;

/// Test implementation of LSP manager that simulates LSP responses
pub struct LSPManager {
    workspace_root: PathBuf,
}

impl LSPManager {
    pub fn new(workspace_root: PathBuf) -> Self {
        Self {
            workspace_root,
        }
    }

    pub async fn initialize_workspace(&self, workspace_root: &PathBuf) -> Result<(), String> {
        debug!("LSPManager initializing workspace: {:?}", workspace_root);
        if !workspace_root.exists() {
            debug!("Workspace root does not exist: {:?}", workspace_root);
            return Err("Workspace root does not exist".to_string());
        }

        // In a real implementation, this would connect to the running LSP server
        // For testing, we just verify the workspace exists
        debug!("Workspace initialized successfully");
        Ok(())
    }

    pub async fn get_workspace_symbols(&self, query: &str) -> Result<Vec<Symbol>, String> {
        debug!("Searching for symbols matching query: {}", query);
        
        // For testing, return User struct and User::new method to match relationship analyzer's expectations
        let mut symbols = vec![
            Symbol {
                id: SymbolId("User".to_string()),
                name: "User".to_string(),
                kind: SymbolKind::Struct,
                location: Location {
                    path: self.workspace_root.join("test.rs"),
                    start: 0,
                    end: 10,
                },
                workspace_path: self.workspace_root.clone(),
            },
            Symbol {
                id: SymbolId("User::new".to_string()),
                name: "new".to_string(),
                kind: SymbolKind::Method,
                location: Location {
                    path: self.workspace_root.join("test.rs"),
                    start: 20,
                    end: 30,
                },
                workspace_path: self.workspace_root.clone(),
            }
        ];

        // Filter based on query
        if !query.is_empty() {
            symbols.retain(|s| s.name.contains(query) || s.id.0.contains(query));
        }

        Ok(symbols)
    }

    pub async fn find_references(&self, symbol_id: &SymbolId) -> Result<Vec<Location>, String> {
        debug!("Finding references for symbol: {:?}", symbol_id);
        
        // For testing, return references that will create relationships
        match symbol_id.0.as_str() {
            "User::new" => Ok(vec![Location {
                path: self.workspace_root.join("test.rs"),
                start: 0,
                end: 10,
            }]),
            "User" => Ok(vec![Location {
                path: self.workspace_root.join("test.rs"),
                start: 20,
                end: 30,
            }]),
            _ => Ok(Vec::new())
        }
    }

    pub async fn get_symbol_at_location(&self, location: &Location) -> Result<Option<Symbol>, String> {
        debug!("Getting symbol at location: {:?}", location);
        
        // For testing, return User struct or new method based on location
        if location.start == 0 {
            Ok(Some(Symbol {
                id: SymbolId("User".to_string()),
                name: "User".to_string(),
                kind: SymbolKind::Struct,
                location: location.clone(),
                workspace_path: self.workspace_root.clone(),
            }))
        } else {
            Ok(Some(Symbol {
                id: SymbolId("User::new".to_string()),
                name: "new".to_string(),
                kind: SymbolKind::Method,
                location: location.clone(),
                workspace_path: self.workspace_root.clone(),
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[tokio::test]
    async fn test_initialize_workspace() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let manager = LSPManager::new(workspace_root.clone());

        let result = manager.initialize_workspace(&workspace_root).await;
        assert!(result.is_ok(), "Failed to initialize: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_get_workspace_symbols() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let manager = LSPManager::new(workspace_root.clone());

        // Test with empty query - should return all symbols
        let symbols = manager.get_workspace_symbols("").await.unwrap();
        assert_eq!(symbols.len(), 2);
        assert!(symbols.iter().any(|s| s.name == "User" && s.kind == SymbolKind::Struct));
        assert!(symbols.iter().any(|s| s.name == "new" && s.kind == SymbolKind::Method));

        // Test with specific query - should match both User and User::new
        let symbols = manager.get_workspace_symbols("User").await.unwrap();
        assert_eq!(symbols.len(), 2);
        assert!(symbols.iter().any(|s| s.name == "User" && s.kind == SymbolKind::Struct));
        assert!(symbols.iter().any(|s| s.name == "new" && s.kind == SymbolKind::Method));

        // Test with non-matching query
        let symbols = manager.get_workspace_symbols("nonexistent").await.unwrap();
        assert!(symbols.is_empty());
    }

    #[tokio::test]
    async fn test_find_references() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let manager = LSPManager::new(workspace_root.clone());

        // Test User::new references
        let references = manager
            .find_references(&SymbolId("User::new".to_string()))
            .await
            .unwrap();
        assert_eq!(references.len(), 1);
        assert_eq!(references[0].start, 0);

        // Test User references
        let references = manager
            .find_references(&SymbolId("User".to_string()))
            .await
            .unwrap();
        assert_eq!(references.len(), 1);
        assert_eq!(references[0].start, 20);

        // Test non-matching symbol
        let references = manager
            .find_references(&SymbolId("nonexistent".to_string()))
            .await
            .unwrap();
        assert!(references.is_empty());
    }

    #[tokio::test]
    async fn test_get_symbol_at_location() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let manager = LSPManager::new(workspace_root.clone());

        // Test getting User struct
        let location = Location {
            path: workspace_root.join("test.rs"),
            start: 0,
            end: 10,
        };
        let result = manager.get_symbol_at_location(&location).await.unwrap();
        assert!(result.is_some());
        let symbol = result.unwrap();
        assert_eq!(symbol.name, "User");
        assert_eq!(symbol.kind, SymbolKind::Struct);

        // Test getting new method
        let location = Location {
            path: workspace_root.join("test.rs"),
            start: 20,
            end: 30,
        };
        let result = manager.get_symbol_at_location(&location).await.unwrap();
        assert!(result.is_some());
        let symbol = result.unwrap();
        assert_eq!(symbol.name, "new");
        assert_eq!(symbol.kind, SymbolKind::Method);
    }
}
