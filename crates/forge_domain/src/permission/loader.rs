use std::path::{Path, PathBuf};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::types::PermissionConfig;

const CONFIG_DIR: &str = ".code-forge";
const CONFIG_FILE: &str = "permissions.yml";

#[derive(Debug, Serialize, Deserialize)]
pub struct PermissionConfigFile {
    pub permission_config: PermissionConfig,
}

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("Failed to read config file: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("Failed to parse YAML: {0}")]
    YamlError(#[from] serde_yaml::Error),
}

/// Find config file in .code-forge directory
pub async fn find_config_file() -> Option<PathBuf> {
    let config_path = PathBuf::from(CONFIG_DIR).join(CONFIG_FILE);
    if tokio::fs::try_exists(&config_path).await.unwrap_or(false) {
        Some(config_path)
    } else {
        None
    }
}

/// Load permission configuration from a YAML file
pub async fn load_config<P: AsRef<Path>>(path: P) -> Result<PermissionConfig, LoadError> {
    let contents = tokio::fs::read_to_string(&path).await?;
    let config_file: PermissionConfigFile = serde_yaml::from_str(&contents)?;
    Ok(config_file.permission_config)
}

/// Attempt to load config from .code-forge/permissions.yml, falling back to defaults
pub async fn load_or_default() -> PermissionConfig {
    if let Some(path) = find_config_file().await {
        let path_display = path.display().to_string();
        match load_config(&path).await {
            Ok(config) => {
                tracing::info!("Loaded permissions from {}", path_display);
                return config;
            }
            Err(e) => {
                tracing::warn!("Error loading permissions from {}: {}", path_display, e);
            }
        }
    }
    tracing::info!("Using default permissions (no config file found at .code-forge/permissions.yml)");
    PermissionConfig::default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;
    use std::fs;
    use std::io::Write;

    // Helper function to create test config - modified to return both paths
    async fn setup_test_config(dir: &TempDir, content: &str) -> (PathBuf, PathBuf) {
        let config_dir = dir.path().join(".code-forge");
        fs::create_dir_all(&config_dir).unwrap();
        let config_path = config_dir.join("permissions.yml");
        
        let mut file = fs::File::create(&config_path).unwrap();
        write!(file, "{}", content).unwrap();
        
        (dir.path().to_path_buf(), config_path)
    }

    #[tokio::test]
    async fn test_load_valid_config() {
        let temp = TempDir::new().unwrap();
        let config_yaml = r#"
permission_config:
  default_policy: Session
  permissions:
    Read: Always
    Write: Session
  deny_patterns:
    - "**/node_modules/**"
"#;
        let (_, config_path) = setup_test_config(&temp, config_yaml).await;
        
        // No more directory changing, just load the config directly
        let config = load_config(config_path).await.unwrap();
        assert_eq!(config.default_policy, super::super::types::Policy::Session);
    }

    #[tokio::test]
    async fn test_load_invalid_config() {
        let temp = TempDir::new().unwrap();
        let config_yaml = "invalid: yaml: content";
        let (_, config_path) = setup_test_config(&temp, config_yaml).await;
        
        assert!(load_config(config_path).await.is_err());
    }

    // Mock implementation of find_config_file for testing
    async fn test_find_config_file(base_path: &Path) -> Option<PathBuf> {
        let config_path = base_path.join(".code-forge").join("permissions.yml");
        if tokio::fs::try_exists(&config_path).await.unwrap_or(false) {
            Some(config_path)
        } else {
            None
        }
    }

    #[tokio::test]
    async fn test_load_or_default() {
        let temp = TempDir::new().unwrap();
        
        // Test with no config
        let config = load_or_default().await;
        assert_eq!(config.default_policy, super::super::types::Policy::Session);
        assert!(config.permissions.is_empty());
        
        // Create valid config and test again
        let config_yaml = r#"
permission_config:
  default_policy: Once
  permissions:
    Read: Always
  deny_patterns: []
"#;
        let (base_path, _) = setup_test_config(&temp, config_yaml).await;
        
        // Mock the find_config_file function for testing
        let found_config = test_find_config_file(&base_path).await.unwrap();
        let config = load_config(found_config).await.unwrap();
        assert_eq!(config.default_policy, super::super::types::Policy::Once);
    }
}
