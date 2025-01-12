use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, Read};

use async_trait::async_trait;
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use forge_domain::{Permission, PermissionResult, PermissionStorage, PermissionError};

/// Storage format for permissions in YAML
#[derive(Debug, Serialize, Deserialize)]
struct StorageFormat {
    version: u32,
    #[serde(default)]
    permissions: HashMap<String, Permission>,
}

impl Default for StorageFormat {
    fn default() -> Self {
        Self {
            version: 1,
            permissions: HashMap::new(),
        }
    }
}

/// Config-based permission storage using YAML files
#[derive(Debug)]
pub struct ConfigStorage {
    config_path: PathBuf,
}

impl ConfigStorage {
    /// Create new config storage with specified path
    pub fn new<P: AsRef<Path>>(config_path: P) -> Self {
        Self {
            config_path: config_path.as_ref().to_path_buf(),
        }
    }

    /// Create storage directory if it doesn't exist
    fn ensure_storage_dir(&self) -> io::Result<()> {
        if let Some(parent) = self.config_path.parent() {
            fs::create_dir_all(parent)?;
        }
        Ok(())
    }

    /// Load the storage format from file
    fn load_storage(&self) -> PermissionResult<StorageFormat> {
        // Ensure file exists
        if !self.config_path.exists() {
            return Ok(StorageFormat::default());
        }

        // Open and lock file
        let mut file = File::open(&self.config_path)
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;
        
        file.lock_shared()
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;

        // Read content
        let mut content = String::new();
        file.read_to_string(&mut content)
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;

        // Parse YAML
        serde_yaml::from_str(&content)
            .map_err(|e| PermissionError::StorageError(e.to_string()))
    }

    /// Save the storage format to file
    fn save_storage(&self, storage: &StorageFormat) -> PermissionResult<()> {
        // Ensure directory exists
        self.ensure_storage_dir()
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;

        // Create/open file with write permissions
        let file = File::create(&self.config_path)
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;
        
        // Lock file for writing
        file.lock_exclusive()
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;

        // Serialize and write
        serde_yaml::to_writer(file, storage)
            .map_err(|e| PermissionError::StorageError(e.to_string()))?;

        Ok(())
    }

    /// Generate storage key from path and tool
    fn make_key(path: &Path, tool: &str) -> String {
        format!("{}:{}", path.to_string_lossy(), tool)
    }
}

#[async_trait]
impl PermissionStorage for ConfigStorage {
    async fn load(
        &self,
        path: &Path,
        tool: &str,
    ) -> PermissionResult<Option<Permission>> {
        let storage = self.load_storage()?;
        let key = Self::make_key(path, tool);
        Ok(storage.permissions.get(&key).cloned())
    }

    async fn save(
        &self,
        permission: Permission,
    ) -> PermissionResult<()> {
        // Load existing storage
        let mut storage = self.load_storage()?;

        // Create key from permission
        let key = Self::make_key(
            permission.path(),
            permission.tool_name(),
        );

        // Update storage
        storage.permissions.insert(key, permission);

        // Save back to file
        self.save_storage(&storage)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use forge_domain::PermissionState;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_config_storage_lifecycle() -> PermissionResult<()> {
        // Create temp directory
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("permissions.yml");
        
        // Create storage
        let storage = ConfigStorage::new(&config_path);

        // Test empty state
        let result = storage
            .load(Path::new("/test/path"), "test_tool")
            .await?;
        assert!(result.is_none());

        // Create test permission
        let permission = Permission::new(
            PermissionState::AllowForever,
            "/test/path",
            "test_tool",
        );

        // Save permission
        storage.save(permission.clone()).await?;

        // Load and verify
        let loaded = storage
            .load(Path::new("/test/path"), "test_tool")
            .await?;
        assert_eq!(loaded, Some(permission));

        Ok(())
    }

    #[tokio::test]
    async fn test_config_storage_multiple_permissions() -> PermissionResult<()> {
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("permissions.yml");
        let storage = ConfigStorage::new(&config_path);

        // Create multiple permissions
        let permission1 = Permission::new(
            PermissionState::AllowForever,
            "/test/path1",
            "tool1",
        );
        let permission2 = Permission::new(
            PermissionState::AllowForever,
            "/test/path2",
            "tool2",
        );

        // Save both
        storage.save(permission1.clone()).await?;
        storage.save(permission2.clone()).await?;

        // Verify both exist
        let loaded1 = storage
            .load(Path::new("/test/path1"), "tool1")
            .await?;
        let loaded2 = storage
            .load(Path::new("/test/path2"), "tool2")
            .await?;

        assert_eq!(loaded1, Some(permission1));
        assert_eq!(loaded2, Some(permission2));

        Ok(())
    }

    #[tokio::test]
    async fn test_config_storage_update_permission() -> PermissionResult<()> {
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("permissions.yml");
        let storage = ConfigStorage::new(&config_path);

        // Initial permission
        let permission1 = Permission::new(
            PermissionState::Allow,
            "/test/path",
            "test_tool",
        );
        storage.save(permission1).await?;

        // Updated permission
        let permission2 = Permission::new(
            PermissionState::AllowForever,
            "/test/path",
            "test_tool",
        );
        storage.save(permission2.clone()).await?;

        // Should get updated version
        let loaded = storage
            .load(Path::new("/test/path"), "test_tool")
            .await?;
        assert_eq!(loaded, Some(permission2));

        Ok(())
    }

    #[tokio::test]
    async fn test_config_storage_invalid_path() -> PermissionResult<()> {
        let temp_dir = tempdir().unwrap();
        let invalid_path = temp_dir.path().join("nonexistent/permissions.yml");
        let storage = ConfigStorage::new(invalid_path);

        // Should start empty
        let result = storage
            .load(Path::new("/test/path"), "test_tool")
            .await?;
        assert!(result.is_none());

        // Should create parent directories
        let permission = Permission::new(
            PermissionState::AllowForever,
            "/test/path",
            "test_tool",
        );
        storage.save(permission.clone()).await?;

        // Should load successfully
        let loaded = storage
            .load(Path::new("/test/path"), "test_tool")
            .await?;
        assert_eq!(loaded, Some(permission));

        Ok(())
    }
}