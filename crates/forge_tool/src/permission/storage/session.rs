use std::path::Path;
use std::collections::HashMap;
use std::sync::Arc;

use async_trait::async_trait;
use tokio::sync::RwLock;
use forge_domain::{Permission, PermissionResult, PermissionStorage};

/// Thread-safe storage for session-level permissions
pub struct SessionStorage {
    /// Inner storage using RwLock for safe concurrent access
    permissions: Arc<RwLock<HashMap<(String, String), Permission>>>,
}

impl SessionStorage {
    /// Create a new empty session storage
    pub fn new() -> Self {
        Self {
            permissions: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Clear all stored permissions
    pub async fn clear(&self) -> PermissionResult<()> {
        let mut permissions = self.permissions.write().await;
        permissions.clear();
        Ok(())
    }

    /// Get the number of stored permissions
    pub async fn len(&self) -> usize {
        self.permissions.read().await.len()
    }

    /// Check if storage is empty
    pub async fn is_empty(&self) -> bool {
        self.permissions.read().await.is_empty()
    }

    /// Create a storage key from path and tool
    fn make_key(path: &Path, tool: &str) -> (String, String) {
        (path.to_string_lossy().to_string(), tool.to_string())
    }
}

#[async_trait]
impl PermissionStorage for SessionStorage {
    async fn load(
        &self,
        path: &Path,
        tool: &str,
    ) -> PermissionResult<Option<Permission>> {
        let key = Self::make_key(path, tool);
        let permissions = self.permissions.read().await;
        Ok(permissions.get(&key).cloned())
    }

    async fn save(
        &self,
        permission: Permission,
    ) -> PermissionResult<()> {
        let key = Self::make_key(
            permission.path(),
            permission.tool_name(),
        );
        let mut permissions = self.permissions.write().await;
        permissions.insert(key, permission);
        Ok(())
    }
}

impl Default for SessionStorage {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use forge_domain::PermissionState;

    #[tokio::test]
    async fn test_session_storage_lifecycle() {
        let storage = SessionStorage::new();
        assert!(storage.is_empty().await);

        let permission = Permission::new(
            PermissionState::Allow,
            "/test/path",
            "test_tool",
        );

        // Create path and tool before permission is moved
        let path = permission.path().to_path_buf();
        let tool = permission.tool_name().to_string();

        // Save permission
        storage.save(permission.clone()).await.unwrap();
        assert_eq!(storage.len().await, 1);

        // Load permission
        let loaded = storage
            .load(&path, &tool)
            .await
            .unwrap();
        assert_eq!(loaded, Some(permission.clone()));

        // Clear storage
        storage.clear().await.unwrap();
        assert!(storage.is_empty().await);

        // Load after clear
        let loaded = storage
            .load(&path, &tool)
            .await
            .unwrap();
        assert_eq!(loaded, None);
    }

    #[tokio::test]
    async fn test_session_storage_concurrent_access() {
        let storage = Arc::new(SessionStorage::new());
        let storage2 = storage.clone();

        // Spawn task to write permission
        let write_task = tokio::spawn(async move {
            let permission = Permission::new(
                PermissionState::Allow,
                "/test/path",
                "test_tool",
            );
            storage2.save(permission).await.unwrap();
        });

        // Read task in main thread
        let read_task = async {
            let loaded = storage
                .load(Path::new("/test/path"), "test_tool")
                .await
                .unwrap();
            loaded
        };

        // Wait for write to complete
        write_task.await.unwrap();

        // Now read
        let loaded = read_task.await;
        assert!(loaded.is_some());
        assert_eq!(loaded.unwrap().tool_name(), "test_tool");
    }

    #[tokio::test]
    async fn test_session_storage_overwrite() {
        let storage = SessionStorage::new();

        // Initial permission
        let permission1 = Permission::new(
            PermissionState::Allow,
            "/test/path",
            "test_tool",
        );
        storage.save(permission1).await.unwrap();

        // Overwrite with new permission
        let permission2 = Permission::new(
            PermissionState::AllowSession,
            "/test/path",
            "test_tool",
        );
        storage.save(permission2.clone()).await.unwrap();

        // Should only have one entry
        assert_eq!(storage.len().await, 1);

        // Should get updated permission
        let loaded = storage
            .load(Path::new("/test/path"), "test_tool")
            .await
            .unwrap();
        assert_eq!(loaded, Some(permission2));
    }

    #[tokio::test]
    async fn test_session_storage_clear_empty() {
        let storage = SessionStorage::new();

        // Clear empty storage should work
        assert!(storage.clear().await.is_ok());
        assert!(storage.is_empty().await);

        // Save something
        let permission = Permission::new(
            PermissionState::Allow,
            "/test/path",
            "test_tool",
        );
        storage.save(permission).await.unwrap();
        assert!(!storage.is_empty().await);

        // Clear again
        assert!(storage.clear().await.is_ok());
        assert!(storage.is_empty().await);
    }
}