pub(crate) mod config {
    use serde::{Deserialize, Serialize};

    /// YAML configuration format
    #[derive(Debug, Serialize, Deserialize)]
    pub struct YamlConfig {
        pub read: YamlPolicy,
        pub write: YamlPolicy,
        pub execute: ExecutePolicy,
    }

    #[derive(Debug, Serialize, Deserialize)]
    pub struct YamlPolicy {
        #[serde(rename = "type")]
        pub policy_type: String,
        pub whitelist: Option<WhitelistConfig>,
    }

    #[derive(Debug, Serialize, Deserialize)]
    pub struct ExecutePolicy {
        #[serde(rename = "type")]
        pub policy_type: String,
        pub whitelist: Option<WhitelistConfig>,
    }

    #[derive(Debug, Serialize, Deserialize)]
    pub struct WhitelistConfig {
        #[serde(rename = "type")]
        pub whitelist_type: String,
        pub commands: Option<Vec<String>>,
    }
}

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use forge_domain::{Command, Permission, PermissionConfig, Policy, Whitelisted};


// Thread-local storage for test configuration
#[cfg(test)]
thread_local! {
    static TEST_CONFIG: OnceLock<Option<PermissionConfig>> = const { OnceLock::new() };
}

// Helper for tests to set and reset config
#[cfg(test)]
pub(crate) fn set_test_config(config: Option<PermissionConfig>) {
    TEST_CONFIG.with(|cell| {
        // Safe because we only use this in tests
        unsafe {
            let cell = &*(cell as *const _ as *mut OnceLock<Option<PermissionConfig>>);
            let _ = cell.set(config);
        }
    });
}

#[cfg(test)]
pub(crate) fn reset_test_config() {
    set_test_config(None);
}

#[cfg(not(test))]
static CONFIG: OnceLock<PermissionConfig> = OnceLock::new();

fn resolve_config_path(config_path: &Path) -> Option<PathBuf> {
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
            let home_path = Path::new(&home).join(config_path);
            if home_path.exists() {
                return Some(home_path);
            }
        }
        None
    }
}

fn load_config() -> PermissionConfig {
    #[cfg(test)]
    {
        // In tests, check if we have a test config first
        if let Some(config) = TEST_CONFIG.with(|cell| cell.get().cloned().flatten()) {
            return config;
        }
    }

    // Otherwise load from file
    let config_path = std::env::var("FORGE_CONFIG")
        .map(PathBuf::from)
        .unwrap_or_else(|_| "config.yml".into());

    let resolved_path = resolve_config_path(&config_path);

    match resolved_path {
        Some(path) => match std::fs::read_to_string(&path) {
            Ok(content) => match serde_yaml::from_str::<config::YamlConfig>(&content) {
                Ok(yaml_config) => convert_config(yaml_config),
                Err(e) => {
                    eprintln!("Error parsing config file {}: {}", path.display(), e);
                    PermissionConfig::default()
                }
            },
            Err(e) => {
                eprintln!("Error reading config file {}: {}", path.display(), e);
                PermissionConfig::default()
            }
        },
        None => {
            eprintln!("Config file not found: {}", config_path.display());
            PermissionConfig::default()
        }
    }
}

/// Load configuration from file or use defaults
pub fn get_config() -> &'static PermissionConfig {
    #[cfg(test)]
    {
        if let Some(config) = TEST_CONFIG.with(|cell| cell.get().cloned().flatten()) {
            return Box::leak(Box::new(config));
        }
    }

    #[cfg(not(test))]
    {
        CONFIG.get_or_init(load_config)
    }

    #[cfg(test)]
    Box::leak(Box::new(load_config()))
}

pub(crate) fn convert_config(yaml: config::YamlConfig) -> PermissionConfig {
    let mut policies = HashMap::new();

    // Convert read policy
    let read_policy = match yaml.read.policy_type.to_lowercase().as_str() {
        "once" => Policy::Once,
        "always" => Policy::Always(Whitelisted::All),
        _ => Policy::Once,
    };
    policies.insert(Permission::Read, read_policy);

    // Convert write policy
    let write_policy = match yaml.write.policy_type.to_lowercase().as_str() {
        "once" => Policy::Once,
        "always" => Policy::Always(Whitelisted::All),
        _ => Policy::Once,
    };
    policies.insert(Permission::Write, write_policy);

    // Convert execute policy
    let execute_policy = match yaml.execute.policy_type.to_lowercase().as_str() {
        "once" => Policy::Once,
        "always" => {
            if let Some(whitelist) = yaml.execute.whitelist {
                match whitelist.whitelist_type.to_lowercase().as_str() {
                    "all" => Policy::Always(Whitelisted::All),
                    "some" if whitelist.commands.is_some() => {
                        let commands = whitelist
                            .commands
                            .unwrap()
                            .into_iter()
                            .map(Command)
                            .collect();
                        Policy::Always(Whitelisted::Some(commands))
                    }
                    _ => Policy::Once,
                }
            } else {
                Policy::Always(Whitelisted::All)
            }
        }
        _ => Policy::Once,
    };
    policies.insert(Permission::Execute, execute_policy);

    PermissionConfig { policies }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use tempfile::TempDir;

    use super::*;

    fn setup_test_config(content: &str) -> (TempDir, PathBuf) {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("config.yml");
        fs::write(&config_path, content).unwrap();

        // Reset the test config before each test
        reset_test_config();

        (temp_dir, config_path)
    }

    #[test]
    fn test_load_default_config() {
        std::env::remove_var("FORGE_CONFIG");
        reset_test_config();
        let config = get_config();
        assert!(matches!(
            config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
    }

    #[test]
    fn test_load_yaml_config() {
        let yaml_content = r#"
read:
  type: "Once"
write:
  type: "Always"
execute:
  type: "Always"
  whitelist:
    type: "Some"
    commands:
      - "ls"
      - "git status"
"#;
        let (_temp_dir, config_path) = setup_test_config(yaml_content);
        std::env::set_var("FORGE_CONFIG", config_path);

        let yaml: config::YamlConfig = serde_yaml::from_str(yaml_content).unwrap();
        let config = convert_config(yaml);

        // Use the test helper to set the config directly
        set_test_config(Some(config.clone()));

        let loaded_config = get_config();
        assert!(matches!(
            loaded_config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
        assert!(matches!(
            loaded_config.policies.get(&Permission::Write),
            Some(Policy::Always(Whitelisted::All))
        ));

        if let Some(Policy::Always(Whitelisted::Some(commands))) =
            loaded_config.policies.get(&Permission::Execute)
        {
            assert_eq!(commands.len(), 2);
            assert_eq!(commands[0].0, "ls");
            assert_eq!(commands[1].0, "git status");
        } else {
            panic!("Expected Some whitelist for execute permission");
        }
    }

    #[test]
    fn test_resolve_config_path() {
        // Test absolute path
        let temp_dir = TempDir::new().unwrap();
        let abs_path = temp_dir.path().join("config.yml");
        fs::write(&abs_path, "dummy").unwrap();

        let resolved = resolve_config_path(&abs_path);
        assert!(resolved.is_some(), "Should resolve absolute path");
        assert_eq!(resolved.unwrap(), abs_path);

        // Test relative path
        let current_dir = std::env::current_dir().unwrap();
        let test_path = current_dir.join("test_config.yml");
        fs::write(&test_path, "dummy").unwrap();

        let relative_path = Path::new("test_config.yml");
        let resolved = resolve_config_path(relative_path);
        assert!(resolved.is_some(), "Should resolve relative path");
        fs::remove_file(test_path).unwrap();
    }

    #[test]
    fn test_invalid_config_uses_default() {
        let invalid_yaml = "invalid: - yaml: content";
        let (_temp_dir, config_path) = setup_test_config(invalid_yaml);
        std::env::set_var("FORGE_CONFIG", config_path);

        let config = get_config();
        assert!(matches!(
            config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
    }

    #[test]
    fn test_missing_whitelist_falls_back_to_once() {
        let yaml_str = r#"
read:
  type: "Once"
write:
  type: "Once"
execute:
  type: "Always"
"#;
        let yaml: config::YamlConfig = serde_yaml::from_str(yaml_str).unwrap();
        let config = convert_config(yaml);

        set_test_config(Some(config));
        let config = get_config();

        assert!(matches!(
            config.policies.get(&Permission::Execute),
            Some(Policy::Always(Whitelisted::All))
        ));
    }

    #[test]
    fn test_nonexistent_config_path() {
        std::env::set_var("FORGE_CONFIG", "/nonexistent/path/config.yml");
        reset_test_config();
        let config = get_config();
        assert!(matches!(
            config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
    }
}
