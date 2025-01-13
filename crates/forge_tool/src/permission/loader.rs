use std::sync::OnceLock;
use forge_domain::{Command, Permission, PermissionConfig, Policy, Whitelisted};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

static CONFIG: OnceLock<PermissionConfig> = OnceLock::new();

/// YAML configuration format
#[derive(Debug, Serialize, Deserialize)]
struct YamlConfig {
    read: YamlPolicy,
    write: YamlPolicy,
    execute: ExecutePolicy,
}

#[derive(Debug, Serialize, Deserialize)]
struct YamlPolicy {
    #[serde(rename = "type")]
    policy_type: String,
    whitelist: Option<WhitelistConfig>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ExecutePolicy {
    #[serde(rename = "type")]
    policy_type: String,
    whitelist: Option<WhitelistConfig>,
}

#[derive(Debug, Serialize, Deserialize)]
struct WhitelistConfig {
    #[serde(rename = "type")]
    whitelist_type: String,
    commands: Option<Vec<String>>,
}

/// Load configuration from file or use defaults
pub fn get_config() -> &'static PermissionConfig {
    CONFIG.get_or_init(|| {
        let config_path = std::env::var("FORGE_CONFIG")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|_| "config.yml".into());

        if config_path.exists() {
            match std::fs::read_to_string(&config_path) {
                Ok(content) => match serde_yaml::from_str::<YamlConfig>(&content) {
                    Ok(yaml_config) => convert_config(yaml_config),
                    Err(_) => PermissionConfig::default(),
                },
                Err(_) => PermissionConfig::default(),
            }
        } else {
            PermissionConfig::default()
        }
    })
}

fn convert_config(yaml: YamlConfig) -> PermissionConfig {
    let mut policies = HashMap::new();

    // Convert read policy
    let read_policy = match yaml.read.policy_type.as_str() {
        "Once" | "once" => Policy::Once,
        "Always" | "always" => Policy::Always(Whitelisted::All),
        _ => Policy::Once,
    };
    policies.insert(Permission::Read, read_policy);

    // Convert write policy
    let write_policy = match yaml.write.policy_type.as_str() {
        "Once" | "once" => Policy::Once,
        "Always" | "always" => Policy::Always(Whitelisted::All),
        _ => Policy::Once,
    };
    policies.insert(Permission::Write, write_policy);

    // Convert execute policy
    let execute_policy = match yaml.execute.policy_type.as_str() {
        "Once" | "once" => Policy::Once,
        "Always" | "always" => {
            if let Some(whitelist) = yaml.execute.whitelist {
                match whitelist.whitelist_type.as_str() {
                    "All" | "all" => Policy::Always(Whitelisted::All),
                    "Some" | "some" if whitelist.commands.is_some() => {
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
                Policy::Once
            }
        }
        _ => Policy::Once,
    };
    policies.insert(Permission::Execute, execute_policy);

    PermissionConfig { policies }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_load_default_config() {
        std::env::remove_var("FORGE_CONFIG");
        let config = get_config();
        assert!(matches!(
            config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
    }

    #[test]
    fn test_load_yaml_config() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("config.yml");
        
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
        fs::write(&config_path, yaml_content).unwrap();
        std::env::set_var("FORGE_CONFIG", config_path);

        let yaml: YamlConfig = serde_yaml::from_str(yaml_content).unwrap();
        let config = convert_config(yaml);

        assert!(matches!(
            config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
        assert!(matches!(
            config.policies.get(&Permission::Write),
            Some(Policy::Always(Whitelisted::All))
        ));

        if let Some(Policy::Always(Whitelisted::Some(commands))) = config.policies.get(&Permission::Execute) {
            assert_eq!(commands.len(), 2);
            assert_eq!(commands[0].0, "ls");
            assert_eq!(commands[1].0, "git status");
        } else {
            panic!("Expected Some whitelist for execute permission");
        }
    }

    #[test]
    fn test_invalid_config_uses_default() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("config.yml");
        
        let invalid_yaml = "invalid: - yaml: content";
        fs::write(&config_path, invalid_yaml).unwrap();
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
        let yaml: YamlConfig = serde_yaml::from_str(yaml_str).unwrap();
        let config = convert_config(yaml);

        assert!(matches!(
            config.policies.get(&Permission::Execute),
            Some(Policy::Once)
        ));
    }
}