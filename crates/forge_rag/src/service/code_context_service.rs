use std::path::PathBuf;
use std::sync::Arc;
use async_trait::async_trait;
use tokio::sync::RwLock;
use tracing::debug;

use forge_domain::{Location, Symbol, SymbolId, SymbolQuery, SymbolRelationship};
use crate::lsp::LSPManager;
use crate::analysis::RelationshipAnalyzer;
use crate::cache::{SymbolCache, NoopSymbolStore};

#[derive(Debug)]
pub struct ServiceError(pub &'static str);

#[async_trait]
pub trait CodeContextService: Send + Sync {
    async fn get_symbol_context(&self, query: &SymbolQuery) -> std::result::Result<Vec<Symbol>, ServiceError>;
    async fn analyze_relationships(&self, symbol: SymbolId) -> std::result::Result<Vec<SymbolRelationship>, ServiceError>;
    async fn find_references(&self, symbol: SymbolId) -> std::result::Result<Vec<Location>, ServiceError>;
    async fn initialize_workspace(&mut self, workspace_root: &PathBuf) -> std::result::Result<(), ServiceError>;
    fn get_workspace_root(&self) -> &PathBuf;
}

pub struct CodeContextServiceImpl {
    lsp_manager: Arc<LSPManager>,
    relationship_analyzer: Arc<RwLock<RelationshipAnalyzer>>,
    symbol_cache: Arc<SymbolCache>,
    workspace_root: PathBuf,
}

impl Default for CodeContextServiceImpl {
    fn default() -> Self {
        // For default initialization, we'll use the current directory
        let workspace_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        Self::with_workspace(workspace_root)
    }
}

impl CodeContextServiceImpl {
    pub fn new(
        lsp_manager: Arc<LSPManager>,
        relationship_analyzer: Arc<RwLock<RelationshipAnalyzer>>,
        symbol_cache: Arc<SymbolCache>,
        workspace_root: PathBuf,
    ) -> Self {
        Self {
            lsp_manager,
            relationship_analyzer,
            symbol_cache,
            workspace_root,
        }
    }

    pub fn with_workspace(workspace_root: PathBuf) -> Self {
        let lsp_manager = Arc::new(LSPManager::new(workspace_root.clone()));
        let relationship_analyzer = Arc::new(RwLock::new(RelationshipAnalyzer::new()));
        let symbol_cache = Arc::new(SymbolCache::new(100, Arc::new(NoopSymbolStore::new())));

        Self {
            lsp_manager,
            relationship_analyzer,
            symbol_cache,
            workspace_root,
        }
    }
}

#[async_trait]
impl CodeContextService for CodeContextServiceImpl {
    async fn get_symbol_context(&self, query: &SymbolQuery) -> std::result::Result<Vec<Symbol>, ServiceError> {
        match query {
            SymbolQuery::Id(id) => {
                if let Some(symbol) = self.symbol_cache.get(&id.0) {
                    Ok(vec![symbol])
                } else {
                    // Try to find it in workspace if not in cache
                    let symbols = self.lsp_manager
                        .get_workspace_symbols(&id.0)
                        .await
                        .map_err(|_| ServiceError("Failed to get workspace symbols"))?;
                    
                    // Cache any found symbols
                    for symbol in symbols.iter().cloned() {
                        self.symbol_cache.as_ref().put(symbol.id.0.clone(), symbol);
                    }
                    
                    Ok(symbols)
                }
            }
            SymbolQuery::Name(name) => {
                let symbols = self.lsp_manager
                    .get_workspace_symbols(name)
                    .await
                    .map_err(|_| ServiceError("Failed to get workspace symbols"))?;
                
                // Cache any found symbols
                for symbol in symbols.iter().cloned() {
                    self.symbol_cache.as_ref().put(symbol.id.0.clone(), symbol);
                }
                
                Ok(symbols)
            }
        }
    }

    async fn analyze_relationships(&self, symbol_id: SymbolId) -> std::result::Result<Vec<SymbolRelationship>, ServiceError> {
        let source = match self.symbol_cache.get(&symbol_id.0) {
            Some(s) => s,
            None => return Ok(vec![]),
        };

        let references = self.lsp_manager
            .find_references(&symbol_id)
            .await
            .map_err(|_| ServiceError("Failed to find references"))?;

        let mut referenced_symbols = Vec::new();
        for location in references {
            if let Ok(Some(symbol)) = self.lsp_manager.get_symbol_at_location(&location).await {
                referenced_symbols.push(symbol);
            }
        }

        let mut analyzer = self.relationship_analyzer.write().await;
        Ok(analyzer.analyze_symbol_relationships(&source, &referenced_symbols))
    }

    async fn find_references(&self, symbol_id: SymbolId) -> std::result::Result<Vec<Location>, ServiceError> {
        self.lsp_manager
            .find_references(&symbol_id)
            .await
            .map_err(|_| ServiceError("Failed to find references"))
    }

    fn get_workspace_root(&self) -> &PathBuf {
        &self.workspace_root
    }

    async fn initialize_workspace(&mut self, workspace_root: &PathBuf) -> std::result::Result<(), ServiceError> {
        debug!("CodeContextService initializing workspace: {:?}", workspace_root);
        
        // Update the workspace root and initialize the LSP server
        self.workspace_root = workspace_root.clone();
        debug!("Initializing LSP manager");
        self.lsp_manager
            .initialize_workspace(&self.workspace_root)
            .await
            .map_err(|e| {
                debug!("LSP manager initialization failed: {}", e);
                ServiceError("Failed to initialize workspace")
            })?;

        // Cache all symbols after initialization
        debug!("Getting all workspace symbols");
        let symbols = self.lsp_manager
            .get_workspace_symbols("")
            .await
            .map_err(|e| {
                debug!("Failed to get workspace symbols: {}", e);
                ServiceError("Failed to get workspace symbols")
            })?;
        debug!("Found {} symbols", symbols.len());

        // Store symbols in cache
        debug!("Caching symbols");
        for symbol in symbols {
            debug!("Caching symbol: {:?}", symbol);
            self.symbol_cache.as_ref().put(symbol.id.0.clone(), symbol);
        }

        debug!("Workspace initialization complete");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[tokio::test]
    async fn test_default() {
        let service = CodeContextServiceImpl::default();
        assert!(service.workspace_root.exists());
    }

    #[tokio::test]
    async fn test_with_workspace() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        
        let service = CodeContextServiceImpl::with_workspace(workspace_root.clone());
        assert_eq!(service.workspace_root, workspace_root);
    }

    #[tokio::test]
    async fn test_get_symbol_context() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let mut service = CodeContextServiceImpl::with_workspace(workspace_root.clone());

        service.initialize_workspace(&workspace_root).await.unwrap();
        let result = service.get_symbol_context(&SymbolQuery::Name("test".to_string())).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_analyze_relationships() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let mut service = CodeContextServiceImpl::with_workspace(workspace_root.clone());

        service.initialize_workspace(&workspace_root).await.unwrap();
        let symbol_id = SymbolId("test".to_string());
        let result = service.analyze_relationships(symbol_id).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_find_references() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let mut service = CodeContextServiceImpl::with_workspace(workspace_root.clone());

        service.initialize_workspace(&workspace_root).await.unwrap();
        let symbol_id = SymbolId("test".to_string());
        let result = service.find_references(symbol_id).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_index_workspace() {
        let temp_dir = TempDir::new().unwrap();
        let workspace_root = temp_dir.path().to_path_buf();
        let mut service = CodeContextServiceImpl::with_workspace(workspace_root.clone());

        let result = service.initialize_workspace(&workspace_root).await;
        assert!(result.is_ok());
    }
}
