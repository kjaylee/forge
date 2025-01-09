use std::sync::Arc;
use std::collections::HashMap;
use std::sync::RwLock;
use forge_domain::Symbol;
use super::symbol_store::SymbolStore;

pub struct SymbolCache {
    capacity: usize,
    store: Arc<dyn SymbolStore>,
    cache: RwLock<HashMap<String, Symbol>>,
}

impl SymbolCache {
    pub fn new(capacity: usize, store: Arc<dyn SymbolStore>) -> Self {
        Self {
            capacity,
            store,
            cache: RwLock::new(HashMap::with_capacity(capacity)),
        }
    }

    pub fn get(&self, key: &str) -> Option<Symbol> {
        // First check in-memory cache
        if let Some(symbol) = self.cache.read().unwrap().get(key) {
            return Some(symbol.clone());
        }

        // If not in cache, check persistent store
        if let Some(symbol) = self.store.get(key) {
            // Add to cache
            let mut cache = self.cache.write().unwrap();
            if cache.len() >= self.capacity {
                // Simple eviction - remove a random entry
                if let Some(k) = cache.keys().next().cloned() {
                    cache.remove(&k);
                }
            }
            cache.insert(key.to_string(), symbol.clone());
            Some(symbol)
        } else {
            None
        }
    }

    pub fn put(&self, key: String, symbol: Symbol) {
        self.store.put(key.clone(), symbol.clone());
        
        let mut cache = self.cache.write().unwrap();
        if cache.len() >= self.capacity {
            if let Some(k) = cache.keys().next().cloned() {
                cache.remove(&k);
            }
        }
        cache.insert(key, symbol);
    }

    pub fn remove(&self, key: &str) -> Option<Symbol> {
        let mut cache = self.cache.write().unwrap();
        cache.remove(key);
        self.store.remove(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache::{NoopSymbolStore, InMemorySymbolStore};
    use forge_domain::{SymbolId, SymbolKind, Location};
    use std::path::PathBuf;

    fn create_test_symbol(id: &str) -> Symbol {
        Symbol {
            id: SymbolId(id.to_string()),
            name: id.to_string(),
            kind: SymbolKind::Function,
            location: Location {
                path: "test.rs".into(),
                start: 0,
                end: 0,
            },
            workspace_path: "test".into(),
        }
    }

    #[test]
    fn test_cache_with_noop_store() {
        let cache = SymbolCache::new(2, Arc::new(NoopSymbolStore::new()));
        let symbol = create_test_symbol("test1");
        
        cache.put("test1".to_string(), symbol.clone());
        assert!(cache.get("test1").is_some());
        assert!(cache.get("nonexistent").is_none());
    }

    #[test]
    fn test_cache_eviction() {
        let cache = SymbolCache::new(2, Arc::new(InMemorySymbolStore::new()));
        
        let symbol1 = create_test_symbol("test1");
        let symbol2 = create_test_symbol("test2");
        let symbol3 = create_test_symbol("test3");
        
        cache.put("test1".to_string(), symbol1);
        cache.put("test2".to_string(), symbol2);
        cache.put("test3".to_string(), symbol3);

        assert!(cache.get("test3").is_some());
        assert!(cache.get("test2").is_some());
        // test1 should have been evicted from cache but still be in store
        assert!(cache.get("test1").is_some());
    }

    #[test]
    fn test_remove() {
        let cache = SymbolCache::new(2, Arc::new(InMemorySymbolStore::new()));
        let symbol = create_test_symbol("test1");
        
        cache.put("test1".to_string(), symbol.clone());
        assert!(cache.get("test1").is_some());
        
        cache.remove("test1");
        assert!(cache.get("test1").is_none());
    }
}