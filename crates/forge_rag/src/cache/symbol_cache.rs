use std::collections::HashMap;
use std::sync::RwLock;
use forge_domain::Symbol;

pub trait SymbolStore: Send + Sync {
    fn get(&self, key: &str) -> Option<Symbol>;
    fn put(&self, key: String, symbol: Symbol);
    fn remove(&self, key: &str) -> Option<Symbol>;
}

pub struct NoopSymbolStore;

impl NoopSymbolStore {
    pub fn new() -> Self {
        Self
    }
}

impl SymbolStore for NoopSymbolStore {
    fn get(&self, _key: &str) -> Option<Symbol> {
        None
    }

    fn put(&self, _key: String, _symbol: Symbol) {}

    fn remove(&self, _key: &str) -> Option<Symbol> {
        None
    }
}

pub struct InMemorySymbolStore {
    store: RwLock<HashMap<String, Symbol>>,
}

impl InMemorySymbolStore {
    pub fn new() -> Self {
        Self {
            store: RwLock::new(HashMap::new()),
        }
    }
}

impl SymbolStore for InMemorySymbolStore {
    fn get(&self, key: &str) -> Option<Symbol> {
        self.store.read().unwrap().get(key).cloned()
    }

    fn put(&self, key: String, symbol: Symbol) {
        self.store.write().unwrap().insert(key, symbol);
    }

    fn remove(&self, key: &str) -> Option<Symbol> {
        self.store.write().unwrap().remove(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use forge_domain::rag::{SymbolId, SymbolKind, Location};

    #[test]
    fn test_noop_store() {
        let store = NoopSymbolStore::new();
        let symbol = Symbol {
            id: SymbolId("test".to_string()),
            name: "test".to_string(),
            kind: SymbolKind::Function,
            location: Location {
                path: "test.rs".into(),
                start: 0,
                end: 0,
            },
            workspace_path: "test".into(),
        };

        store.put("test".to_string(), symbol.clone());
        assert!(store.get("test").is_none());
        assert!(store.remove("test").is_none());
    }

    #[test]
    fn test_in_memory_store() {
        let store = InMemorySymbolStore::new();
        let symbol = Symbol {
            id: SymbolId("test".to_string()),
            name: "test".to_string(),
            kind: SymbolKind::Function,
            location: Location {
                path: "test.rs".into(),
                start: 0,
                end: 0,
            },
            workspace_path: "test".into(),
        };

        store.put("test".to_string(), symbol.clone());
        assert_eq!(store.get("test").unwrap().name, "test");
        assert_eq!(store.remove("test").unwrap().name, "test");
        assert!(store.get("test").is_none());
    }
}