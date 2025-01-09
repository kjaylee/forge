use std::path::PathBuf;
use super::{symbol::Symbol, relationship::SymbolRelationship};

#[derive(Debug, Clone)]
pub struct CodeContext {
    pub symbols: Vec<Symbol>,
    pub relationships: Vec<SymbolRelationship>,
    pub workspace_root: PathBuf,
}

impl CodeContext {
    pub fn new(
        symbols: Vec<Symbol>,
        relationships: Vec<SymbolRelationship>,
        workspace_root: PathBuf,
    ) -> Self {
        Self {
            symbols,
            relationships,
            workspace_root,
        }
    }

    pub fn empty(workspace_root: PathBuf) -> Self {
        Self {
            symbols: Vec::new(),
            relationships: Vec::new(),
            workspace_root,
        }
    }
}