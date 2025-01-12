use std::path::{Path, PathBuf};
use std::collections::HashMap;
use tokio::fs::{self, File as TokioFile};
use tokio::io::AsyncReadExt;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use forge_domain::{Permission, PermissionResult, PermissionStorage, PermissionError};
use std::io::{BufWriter, Write};

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
    async fn ensure_storage_dir(&self) -> PermissionResult<()> {
        if let Some(parent) = self.config_path.parent() {
            fs::create_dir_all(parent).await?;
        }
        Ok(())
    }

    /// Load the storage format from file
    async fn load_storage(&self) -> PermissionResult<StorageFormat> {
        tracing::debug!("Loading storage from: {:?}", self.config_path);

        // Ensure file exists
        if !self.config_path.exists() {
            tracing::debug!("Config file does not exist, returning default storage");
            return Ok(StorageFormat::default());
        }

        // Open and lock file
        let mut file = TokioFile::open(&self.config_path).await
            .map_err(|e| {
                tracing::error!("Failed to open config file: {}", e);
                PermissionError::StorageError(e.to_string())
            })?;

        // Read content
        let mut content = String::new();
        file.read_to_string(&mut content).await
            .map_err(|e| {
                tracing::error!("Failed to read config file: {}", e);
                PermissionError::StorageError(e.to_string())
            })?;

        tracing::debug!("Read config file content:\n{}", content);

        // Parse YAML
        let storage: StorageFormat = serde_yaml::from_str(&content)
            .map_err(|e| {
                tracing::error!("Failed to parse YAML: {}", e);
                PermissionError::StorageError(e.to_string())
            })?;

        tracing::debug!("Loaded {} permissions from storage", storage.permissions.len());
        Ok(storage)
    }

    /// Save the storage format to file
    async fn save_storage(&self, storage: &StorageFormat) -> PermissionResult<()> {
        tracing::debug!("Saving storage to: {:?}", self.config_path);
        tracing::debug!("Storage contains {} permissions", storage.permissions.len());
        for (key, permission) in &storage.permissions {
            tracing::debug!("Permission: {} -> {:?}", key, permission);
        }

        // Ensure directory exists
        self.ensure_storage_dir().await
            .map_err(|e| {
                tracing::error!("Failed to create directory: {}", e);
                PermissionError::StorageError(e.to_string())
            })?;

        // Create/open file with write permissions
        let file = tokio::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&self.config_path)
            .await
            .map_err(|e| {
                tracing::error!("Failed to open file for writing: {}", e);
                PermissionError::StorageError(e.to_string())
            })?;

        // Convert to sync file for serde_yaml
        let std_file = file.into_std().await;
        
        // Write YAML with pretty formatting
        let yaml = serde_yaml::to_string(storage)
            .map_err(|e| {
                tracing::error!("Failed to serialize storage to YAML: {}", e);
                PermissionError::StorageError(e.to_string())
            })?;
        
        tracing::debug!("Writing YAML content:\n{}", yaml);

        // Write to file in a separate scope to ensure writer is dropped
        {
            let mut writer = BufWriter::new(std_file);
            writer.write_all(yaml.as_bytes())
                .map_err(|e| {
                    tracing::error!("Failed to write to file: {}", e);
                    PermissionError::StorageError(e.to_string())
                })?;
            writer.flush()
                .map_err(|e| {
                    tracing::error!("Failed to flush writer: {}", e);
                    PermissionError::StorageError(e.to_string())
                })?;
        }

        // Verify the file was written after writer is dropped
        match tokio::fs::read_to_string(&self.config_path).await {
            Ok(content) => {
                tracing::debug!("Verified file content:\n{}", content);
                // Parse the content to ensure it's valid YAML
                if let Err(e) = serde_yaml::from_str::<StorageFormat>(&content) {
                    tracing::error!("Written content is not valid YAML: {}", e);
                    return Err(PermissionError::StorageError("Written content is not valid YAML".to_string()));
                }
            }
            Err(e) => {
                tracing::error!("Failed to verify file content after writing: {}", e);
                return Err(PermissionError::StorageError("Failed to verify written content".to_string()));
            }
        }

        tracing::debug!("Successfully saved storage");
        Ok(())
    }

    /// Generate storage key from path and tool
    fn make_key(path: &Path, tool: &str) -> String {
        tracing::debug!("Generating key for path: {:?}, tool: {}", path, tool);

        // If path is relative, make it absolute using current directory
        let abs_path = if path.is_relative() {
            if let Ok(cwd) = std::env::current_dir() {
                let path = cwd.join(path);
                tracing::debug!("Made relative path absolute: {:?}", path);
                path
            } else {
                tracing::debug!("Could not get current directory, using original path");
                path.to_path_buf()
            }
        } else {
            tracing::debug!("Path is already absolute");
            path.to_path_buf()
        };

        // Try to canonicalize the path, fall back to original if it fails
        let path_str = match std::fs::canonicalize(&abs_path) {
            Ok(p) => {
                tracing::debug!("Canonicalized path: {:?}", p);
                p.to_string_lossy().to_string()
            }
            Err(e) => {
                tracing::debug!("Failed to canonicalize path: {}", e);
                abs_path.to_string_lossy().to_string()
            }
        };

        let key = format!("{}:{}", path_str, tool);
        tracing::debug!("Generated key: {}", key);
        key
    }
}

#[async_trait]
impl PermissionStorage for ConfigStorage {
    async fn load(
        &self,
        path: &Path,
        tool: &str,
    ) -> PermissionResult<Option<Permission>> {
        tracing::debug!("Loading permission for path: {:?}, tool: {}", path, tool);
        let storage = self.load_storage().await?;
        let key = Self::make_key(path, tool);
        tracing::debug!("Looking up permission with key: {}", key);
        let result = storage.permissions.get(&key).cloned();
        tracing::debug!("Found permission: {:?}", result);
        Ok(result)
    }

    async fn save(
        &self,
        mut permission: Permission,
    ) -> PermissionResult<()> {
        tracing::debug!("Saving permission for path: {:?}", permission.path());

        // Load existing storage
        let mut storage = self.load_storage().await?;

        // Make path absolute if it's relative
        let abs_path = if permission.path().is_relative() {
            if let Ok(cwd) = std::env::current_dir() {
                let path = cwd.join(permission.path());
                tracing::debug!("Made relative path absolute: {:?}", path);
                path
            } else {
                permission.path().to_path_buf()
            }
        } else {
            tracing::debug!("Path is already absolute");
            permission.path().to_path_buf()
        };

        // Try to canonicalize the path
        let final_path = if let Ok(canonical_path) = std::fs::canonicalize(&abs_path) {
            tracing::debug!("Canonicalized path: {:?}", canonical_path);
            canonical_path
        } else {
            tracing::debug!("Could not canonicalize path, using absolute path");
            abs_path
        };

        // Create new permission with final path
        permission = Permission::new(
            permission.state.clone(),
            final_path,
            permission.tool_name().to_string(),
        );

        // Create key from permission
        let key = Self::make_key(
            permission.path(),
            permission.tool_name(),
        );
        tracing::debug!("Using storage key: {}", key);

        // Update storage
        storage.permissions.insert(key, permission);

        // Save back to file
        tracing::debug!("Saving to config file: {:?}", self.config_path);
        self.save_storage(&storage).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use forge_domain::PermissionState;
    use tempfile::tempdir;
    use std::env;

    #[tokio::test]
    async fn test_relative_path_handling() -> PermissionResult<()> {
        // Create temp directory and set it as current dir
        let temp_dir = tempdir().unwrap();
        env::set_current_dir(&temp_dir).unwrap();
        
        // Create a subdirectory to test relative paths
        let sub_dir = temp_dir.path().join("subdir");
        std::fs::create_dir(&sub_dir).unwrap();
        
        // Create config file in temp dir
        let config_path = temp_dir.path().join("permissions.yml");
        let storage = ConfigStorage::new(&config_path);

        // Create permission with relative path
        let permission = Permission::new(
            PermissionState::AllowForever,
            "subdir/test.txt",  // Relative path
            "test_tool",
        );

        // Save permission
        storage.save(permission.clone()).await?;

        // Try loading with relative path
        let loaded1 = storage
            .load(Path::new("subdir/test.txt"), "test_tool")
            .await?;
        // Normalize paths for comparison by resolving symbolic links
        let temp_path = std::fs::canonicalize(&temp_dir).unwrap();
        let abs_path = temp_path.join("subdir/test.txt");

        // Create new permission with the canonical path
        let expected_permission = Permission::new(
            PermissionState::AllowForever,
            abs_path.clone(),
            "test_tool",
        );

        // Compare paths directly since they might not exist yet
        if let Some(loaded1) = loaded1 {
            let loaded1_path = loaded1.path();
            // Remove /private prefix if present for macOS compatibility
            let loaded1_str = loaded1_path.to_string_lossy();
            let loaded1_str = loaded1_str.strip_prefix("/private").unwrap_or(&loaded1_str);
            let abs_str = abs_path.to_string_lossy();
            let abs_str = abs_str.strip_prefix("/private").unwrap_or(&abs_str);
            assert_eq!(loaded1_str, abs_str);
        } else {
            panic!("Expected permission not found in loaded1");
        }

        // Try loading with absolute path
        let loaded2 = storage
            .load(&abs_path, "test_tool")
            .await?;
            
        if let Some(loaded2) = loaded2 {
            let loaded2_path = loaded2.path();
            // Remove /private prefix if present for macOS compatibility
            let loaded2_str = loaded2_path.to_string_lossy();
            let loaded2_str = loaded2_str.strip_prefix("/private").unwrap_or(&loaded2_str);
            let abs_str = abs_path.to_string_lossy();
            let abs_str = abs_str.strip_prefix("/private").unwrap_or(&abs_str);
            assert_eq!(loaded2_str, abs_str);
        } else {
            panic!("Expected permission not found in loaded2");
        }

        Ok(())
    }

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
    #[tokio::test]
    async fn test_allow_forever_state() -> PermissionResult<()> {
        let temp_dir = tempdir().unwrap();
        let config_path = temp_dir.path().join("permissions.yml");
        let storage = ConfigStorage::new(&config_path);

        // Create permission with AllowForever state
        let permission = Permission::new(
            PermissionState::AllowForever,
            "/test/path",
            "test_tool",
        );

        // Save permission
        storage.save(permission.clone()).await?;

        // Verify the file exists and contains the permission
        let content = tokio::fs::read_to_string(&config_path).await
            .expect("Failed to read config file");
        assert!(content.contains("AllowForever"));

        // Load and verify the state is preserved
        let loaded = storage
            .load(Path::new("/test/path"), "test_tool")
            .await?;
        assert_eq!(loaded, Some(permission));
        assert!(matches!(
            loaded.unwrap().state,
            PermissionState::AllowForever
        ));

        Ok(())
    }
}
