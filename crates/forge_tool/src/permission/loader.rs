use std::{fs, path::PathBuf};

use anyhow::Error;
use forge_domain::{Permission, PermissionConfig, Policy};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct RawConfig {
    read: Policy,
    write: Policy,
    execute: Policy,
}

impl From<RawConfig> for PermissionConfig {
    fn from(raw: RawConfig) -> Self {
        let mut policies = std::collections::HashMap::new();
        // Normalize if needed
        policies.insert(Permission::Read, raw.read.normalize());
        policies.insert(Permission::Write, raw.write.normalize());
        policies.insert(Permission::Execute, raw.execute.normalize());
        PermissionConfig { policies }
    }
}

pub struct PermissionLoader {
    config_path: PathBuf,
}

impl PermissionLoader {
    pub fn new(config_path: PathBuf) -> Self {
        Self { config_path }
    }

    fn resolve_config_path(config_path: &PathBuf) -> Option<PathBuf> {
        if config_path.is_absolute() {
            Some(config_path.to_path_buf())
        } else {
            // Try current directory first
            if let Ok(current_dir) = std::env::current_dir() {
                let path = current_dir.join(config_path);
                if path.exists() {
                    return Some(path);
                }
            }

            // Try home directory next
            if let Some(home) = std::env::var_os("HOME") {
                let home_path = PathBuf::from(home).join(config_path);
                if home_path.exists() {
                    return Some(home_path);
                }
            }
            None
        }
    }

    pub fn load(&self) -> Result<PermissionConfig, Error> {
        let resolved_path = Self::resolve_config_path(&self.config_path)
            .ok_or_else(|| Error::msg("Config file not found"))?;

        let content = fs::read_to_string(&resolved_path)?;
        let raw_config: RawConfig = serde_yaml::from_str(&content)?;
        Ok(raw_config.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use forge_domain::{Permission, Policy, Whitelisted};
    use tempfile::TempDir;
    use std::fs;

    fn setup_test_config(content: &str) -> (TempDir, PathBuf) {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("config.yml");
        fs::write(&config_path, content).unwrap();
        (temp_dir, config_path)
    }

    #[test]
    fn test_load_minimal_config() {
        let yaml_content = r#"
            read: once
            write: once
            execute: once
        "#;
        let (_temp_dir, config_path) = setup_test_config(yaml_content);

        let loader = PermissionLoader::new(config_path);
        let config = loader.load().unwrap();

        assert!(matches!(config.policies.get(&Permission::Read), Some(Policy::Once)));
        assert!(matches!(config.policies.get(&Permission::Write), Some(Policy::Once)));
        assert!(matches!(config.policies.get(&Permission::Execute), Some(Policy::Once)));
    }

    #[test]
    fn test_load_all_config() {
        let yaml_content = r#"
            read:
              Always: All
            write:
              Always: All
            execute:
              Always:
                Some:
                  - "ls"
                  - "git status"
        "#;
        let (_temp_dir, config_path) = setup_test_config(yaml_content);

        let loader = PermissionLoader::new(config_path);
        let config = loader.load().unwrap();

        match config.policies.get(&Permission::Read) {
            Some(Policy::Always(Whitelisted::All)) => (),
            other => panic!("Expected read policy Always(All), got {:?}", other),
        }
        match config.policies.get(&Permission::Write) {
            Some(Policy::Always(Whitelisted::All)) => (),
            other => panic!("Expected write policy Always(All), got {:?}", other),
        }
        match config.policies.get(&Permission::Execute) {
            Some(Policy::Always(Whitelisted::Some(cmds))) => {
                assert_eq!(cmds.len(), 2);
                assert_eq!(cmds[0].0, "ls");
                assert_eq!(cmds[1].0, "git status");
            }
            other => panic!("Expected execute policy Always(Some([...])) got {:?}", other),
        }
    }

    #[test]
    fn test_nonexistent_config() {
        let loader = PermissionLoader::new(PathBuf::from("/nonexistent/config.yml"));
        assert!(loader.load().is_err());
    }

    #[test]
    fn test_invalid_config() {
        let yaml_content = "invalid: - yaml: content";
        let (_temp_dir, config_path) = setup_test_config(yaml_content);

        let loader = PermissionLoader::new(config_path);
        assert!(loader.load().is_err());
    }
}
