use forge_domain::{Permission, PermissionChecker, Policy, Whitelisted};
use tracing::debug;

use crate::permission::loader;

/// Live permission service implementation
#[derive(Clone)]
pub struct LivePermissionService;

impl LivePermissionService {
    /// Create new service instance
    pub fn new() -> Self {
        Self
    }
}

#[async_trait::async_trait]
impl PermissionChecker for LivePermissionService {
    async fn check_permission(&self, perm: Permission, cmd: Option<&str>) -> Result<bool, String> {
        let config = loader::get_config();
        debug!("Checking permission {:?} with command {:?}", perm, cmd);
        debug!("Current config: {:?}", config);

        let result = match config.policies.get(&perm) {
            Some(Policy::Once) => {
                debug!("Policy Once found for {:?}", perm);
                false
            } // Always ask for permission
            Some(Policy::Always(whitelist)) => match (perm, whitelist, cmd) {
                // For Execute permission, check command against whitelist
                (Permission::Execute, _, None) => {
                    debug!("Execute permission without command");
                    false
                } // Execute needs a command
                (Permission::Execute, Whitelisted::All, _) => {
                    debug!("Execute permission with All whitelist");
                    true
                }
                (Permission::Execute, Whitelisted::Some(commands), Some(cmd)) => {
                    let allowed = commands.iter().any(|c| cmd.contains(&c.0));
                    debug!("Execute permission check for {:?}: {:?}", cmd, allowed);
                    allowed
                }
                // For Read/Write, any Always policy grants permission
                (_, Whitelisted::All, _) => {
                    debug!("Always policy (All) for non-execute permission");
                    true
                }
                (_, Whitelisted::Some(_), _) => {
                    debug!("Always policy (Some) for non-execute permission");
                    true
                }
            },
            None => {
                debug!("No policy found for {:?}", perm);
                false
            } // If no policy exists, deny by default
        };

        debug!("Permission check result for {:?}: {:?}", perm, result);
        Ok(result)
    }
}

impl Default for LivePermissionService {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use loader::config::YamlConfig;
    use tempfile::TempDir;

    use super::*;

    fn parse_and_set_config(content: &str) -> TempDir {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("config.yml");
        fs::write(&config_path, content).unwrap();
        std::env::set_var("FORGE_CONFIG", config_path);

        // Parse and set the config directly
        let yaml: YamlConfig = serde_yaml::from_str(content).unwrap();
        let config = loader::convert_config(yaml);
        loader::set_test_config(Some(config));

        temp_dir
    }

    #[tokio::test]
    async fn test_once_permissions() {
        let config = r#"
read:
  type: "Once"
write:
  type: "Once"
execute:
  type: "Once"
"#;
        let _temp_dir = parse_and_set_config(config);
        let service = LivePermissionService::new();

        let read = service.check_permission(Permission::Read, None).await;
        let write = service.check_permission(Permission::Write, None).await;
        let execute = service
            .check_permission(Permission::Execute, Some("ls"))
            .await;

        assert!(matches!(read, Ok(false)), "Read should require asking");
        assert!(matches!(write, Ok(false)), "Write should require asking");
        assert!(
            matches!(execute, Ok(false)),
            "Execute should require asking"
        );
    }

    #[tokio::test]
    async fn test_execute_whitelist() {
        let config = r#"
read:
  type: "Once"
write:
  type: "Once"
execute:
  type: "Always"
  whitelist:
    type: "Some"
    commands:
      - "ls"
      - "git"
"#;
        let _temp_dir = parse_and_set_config(config);
        let service = LivePermissionService::new();

        // Whitelisted command
        let result = service
            .check_permission(Permission::Execute, Some("ls -la"))
            .await;
        assert!(
            matches!(result, Ok(true)),
            "Whitelisted command should be allowed"
        );

        // Non-whitelisted command
        let result = service
            .check_permission(Permission::Execute, Some("rm -rf"))
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Non-whitelisted command should be denied"
        );

        // Missing command
        let result = service.check_permission(Permission::Execute, None).await;
        assert!(
            matches!(result, Ok(false)),
            "Missing command should be denied"
        );
    }

    #[tokio::test]
    async fn test_always_read() {
        let config = r#"
read:
  type: "Always"
write:
  type: "Once"
execute:
  type: "Once"
"#;
        let _temp_dir = parse_and_set_config(config);
        let service = LivePermissionService::new();

        let result = service.check_permission(Permission::Read, None).await;
        assert!(
            matches!(result, Ok(true)),
            "Always policy should allow read"
        );
    }

    #[tokio::test]
    async fn test_config_loading() {
        let config = r#"
read:
  type: "Always"
write:
  type: "Once"
execute:
  type: "Once"
"#;
        let _temp_dir = parse_and_set_config(config);

        // Force config loading and verify it's correct
        let config = loader::get_config();
        println!("Config loaded: {:?}", config);
        assert!(
            config.policies.contains_key(&Permission::Read),
            "Read policy should exist"
        );
        assert!(
            matches!(
                config.policies.get(&Permission::Read),
                Some(Policy::Always(_))
            ),
            "Read policy should be Always"
        );
    }

    #[tokio::test]
    async fn test_mixed_permissions() {
        let config = r#"
read:
  type: "Always"
write:
  type: "Once"
execute:
  type: "Always"
  whitelist:
    type: "Some"
    commands:
      - "ls"
      - "git"
"#;
        let _temp_dir = parse_and_set_config(config);
        let service = LivePermissionService::new();

        let read = service.check_permission(Permission::Read, None).await;
        assert!(matches!(read, Ok(true)), "Read should be allowed");

        let write = service.check_permission(Permission::Write, None).await;
        assert!(matches!(write, Ok(false)), "Write should require asking");

        let allowed_exec = service
            .check_permission(Permission::Execute, Some("ls"))
            .await;
        assert!(
            matches!(allowed_exec, Ok(true)),
            "Allowed command should be permitted"
        );

        let denied_exec = service
            .check_permission(Permission::Execute, Some("rm"))
            .await;
        assert!(
            matches!(denied_exec, Ok(false)),
            "Denied command should be rejected"
        );
    }

    #[tokio::test]
    async fn test_config_case_insensitivity() {
        let config = r#"
read:
  type: "ALWAYS"
write:
  type: "ONCE"
execute:
  type: "ALWAYS"
  whitelist:
    type: "SOME"
    commands:
      - "ls"
"#;
        let _temp_dir = parse_and_set_config(config);
        let service = LivePermissionService::new();

        let read = service.check_permission(Permission::Read, None).await;
        assert!(
            matches!(read, Ok(true)),
            "Case-insensitive Always should allow read"
        );

        let write = service.check_permission(Permission::Write, None).await;
        assert!(
            matches!(write, Ok(false)),
            "Case-insensitive Once should require asking"
        );

        let exec = service
            .check_permission(Permission::Execute, Some("ls"))
            .await;
        assert!(
            matches!(exec, Ok(true)),
            "Case-insensitive whitelist should work"
        );
    }
}
