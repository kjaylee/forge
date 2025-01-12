use std::path::Path;
use async_trait::async_trait;

use super::{Permission, PermissionError, PermissionResult};

/// Error types specific to permission storage operations
#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    /// Error when loading permissions
    #[error("Failed to load permission: {0}")]
    LoadError(String),

    /// Error when saving permissions
    #[error("Failed to save permission: {0}")]
    SaveError(String),

    /// Error when permission data is corrupted
    #[error("Permission data corrupted: {0}")]
    DataError(String),
}

/// Trait for storage implementations that can persist permissions
#[async_trait]
/// Service for storing and retrieving permissions
#[async_trait]
pub trait PermissionStorage: Send + Sync {
    /// Load a permission for a given path and tool if it exists
    /// 
    /// # Arguments
    /// * `path` - The path to check permissions for
    /// * `tool` - The tool name to check permissions for
    /// 
    /// # Returns
    /// * `Ok(Some(Permission))` if permission exists
    /// * `Ok(None)` if no permission exists
    /// * `Err(StorageError)` if there was an error accessing storage
    async fn load(
        &self,
        path: &Path,
        tool: &str,
    ) -> PermissionResult<Option<Permission>>;

    /// Save a permission
    /// 
    /// # Arguments
    /// * `permission` - The permission to save
    /// 
    /// # Returns
    /// * `Ok(())` if save was successful
    /// * `Err(StorageError)` if there was an error saving
    async fn save(
        &self,
        permission: Permission,
    ) -> PermissionResult<()>;
}

impl From<StorageError> for PermissionError {
    fn from(error: StorageError) -> Self {
        match error {
            StorageError::LoadError(msg) => PermissionError::StorageError(msg),
            StorageError::SaveError(msg) => PermissionError::StorageError(msg),
            StorageError::DataError(msg) => PermissionError::StorageError(msg),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use tokio::sync::RwLock;

    /// Mock storage implementation for testing
    pub(crate) struct MockStorage {
        permissions: RwLock<HashMap<(String, String), Permission>>,
        should_fail_load: bool,
        should_fail_save: bool,
    }

    impl MockStorage {
        pub fn new() -> Self {
            Self {
                permissions: RwLock::new(HashMap::new()),
                should_fail_load: false,
                should_fail_save: false,
            }
        }

        /// Create a mock that fails load operations
        pub fn fail_load() -> Self {
            Self {
                permissions: RwLock::new(HashMap::new()),
                should_fail_load: true,
                should_fail_save: false,
            }
        }

        /// Create a mock that fails save operations
        pub fn fail_save() -> Self {
            Self {
                permissions: RwLock::new(HashMap::new()),
                should_fail_load: false,
                should_fail_save: true,
            }
        }

        fn make_key(path: &Path, tool: &str) -> (String, String) {
            (path.to_string_lossy().to_string(), tool.to_string())
        }
    }

    #[async_trait]
    impl PermissionStorage for MockStorage {
        async fn load(
            &self,
            path: &Path,
            tool: &str,
        ) -> PermissionResult<Option<Permission>> {
            if self.should_fail_load {
                return Err(StorageError::LoadError("Simulated load failure".into()).into());
            }

            let key = Self::make_key(path, tool);
            let permissions = self.permissions.read().await;
            Ok(permissions.get(&key).cloned())
        }

        async fn save(
            &self,
            permission: Permission,
        ) -> PermissionResult<()> {
            if self.should_fail_save {
                return Err(StorageError::SaveError("Simulated save failure".into()).into());
            }

            let key = Self::make_key(
                permission.path(),
                permission.tool_name(),
            );
            let mut permissions = self.permissions.write().await;
            permissions.insert(key, permission);
            Ok(())
        }
    }

    #[tokio::test]
    async fn test_mock_storage_load_save() {
        let storage = MockStorage::new();
        let permission = Permission::new(
            super::super::PermissionState::Allow,
            "/test/path",
            "test_tool",
        );

        // Save permission
        storage.save(permission.clone()).await.unwrap();

        // Load permission
        let loaded = storage
            .load(permission.path(), permission.tool_name())
            .await
            .unwrap();

        assert_eq!(loaded, Some(permission));
    }

    #[tokio::test]
    async fn test_mock_storage_missing_permission() {
        let storage = MockStorage::new();
        
        let loaded = storage
            .load(Path::new("/nonexistent"), "no_tool")
            .await
            .unwrap();

        assert_eq!(loaded, None);
    }

    #[tokio::test]
    async fn test_mock_storage_load_failure() {
        let storage = MockStorage::fail_load();
        
        let result = storage
            .load(Path::new("/test"), "test")
            .await;

        assert!(matches!(
            result,
            Err(PermissionError::StorageError(_))
        ));
    }

    #[tokio::test]
    async fn test_mock_storage_save_failure() {
        let storage = MockStorage::fail_save();
        let permission = Permission::new(
            super::super::PermissionState::Allow,
            "/test/path",
            "test_tool",
        );

        let result = storage.save(permission).await;

        assert!(matches!(
            result,
            Err(PermissionError::StorageError(_))
        ));
    }
}
