//! Configuration loading functionality for the permission system.

use std::env;
use std::path::{Path, PathBuf};

use super::{PermissionConfig, PermissionResult, PermissionError};

/// Environment variable for custom config path
pub const FORGE_PERMISSION_CONFIG: &str = "FORGE_PERMISSION_CONFIG";
/// Default config directory name
pub const DEFAULT_CONFIG_DIR: &str = ".code-forge";
/// Default config file name
pub const DEFAULT_CONFIG_FILE: &str = "permissions.yml";

/// Configuration loader for the permission system
#[derive(Debug)]
pub struct ConfigLoader {
    config_path: PathBuf,
}

impl ConfigLoader {
    /// Create a new config loader
    pub fn new() -> PermissionResult<Self> {
        let config_path = Self::resolve_config_path()?;
        Ok(Self { config_path })
    }

    /// Create a new config loader with a specific path
    pub fn with_path<P: AsRef<Path>>(path: P) -> Self {
        Self {
            config_path: path.as_ref().to_path_buf(),
        }
    }

    /// Load the configuration
    pub fn load(&self) -> PermissionResult<PermissionConfig> {
        if !self.config_path.exists() {
            return Ok(PermissionConfig::default());
        }

        let contents = std::fs::read_to_string(&self.config_path)?;
        let config: PermissionConfig = serde_yaml::from_str(&contents)?;
        Ok(config)
    }

    /// Save configuration to file
    pub fn save(&self, config: &PermissionConfig) -> PermissionResult<()> {
        if let Some(parent) = self.config_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        
        let yaml = serde_yaml::to_string(config)?;
        std::fs::write(&self.config_path, yaml)?;
        Ok(())
    }

    /// Get the current config path
    pub fn config_path(&self) -> &Path {
        &self.config_path
    }

    /// Resolve the configuration file path
    fn resolve_config_path() -> PermissionResult<PathBuf> {
        // Check environment variable first
        if let Ok(path) = env::var(FORGE_PERMISSION_CONFIG) {
            return Ok(PathBuf::from(path));
        }

        // Fall back to default location in home directory
        let home_dir = home::home_dir()
            .ok_or(PermissionError::HomeDirectoryNotFound)?;

        Ok(home_dir
            .join(DEFAULT_CONFIG_DIR)
            .join(DEFAULT_CONFIG_FILE))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_default_config_path() {
        let loader = ConfigLoader::new().unwrap();
        let home_dir = home::home_dir().unwrap();
        let expected_path = home_dir
            .join(DEFAULT_CONFIG_DIR)
            .join(DEFAULT_CONFIG_FILE);
        assert_eq!(loader.config_path(), expected_path);
    }

    #[test]
    fn test_env_var_config_path() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("test_config.yml");
        
        env::set_var(FORGE_PERMISSION_CONFIG, config_path.as_os_str());
        let loader = ConfigLoader::new().unwrap();
        assert_eq!(loader.config_path(), config_path);
        env::remove_var(FORGE_PERMISSION_CONFIG);
    }

    #[test]
    fn test_load_nonexistent_config() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("nonexistent.yml");
        
        let loader = ConfigLoader::with_path(config_path);
        let config = loader.load().unwrap();
        assert!(config.tools.is_empty());
    }

    #[test]
    fn test_save_and_load_config() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("test_config.yml");
        
        let loader = ConfigLoader::with_path(config_path);
        let config = PermissionConfig::default();
        
        loader.save(&config).unwrap();
        let loaded_config = loader.load().unwrap();
        
        assert_eq!(
            serde_yaml::to_string(&config).unwrap(),
            serde_yaml::to_string(&loaded_config).unwrap()
        );
    }
}