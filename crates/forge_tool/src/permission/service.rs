use std::path::PathBuf;
use std::sync::Arc;

use forge_domain::{Permission, PermissionChecker, PermissionConfig, Policy};

use crate::Service;

pub trait PermissionService: Send + Sync + PermissionChecker {
    fn get_policy(&self, permission: Permission) -> &Policy;
}

struct Live {
    config: PermissionConfig,
}

impl Live {
    fn new(config: PermissionConfig) -> Self {
        Self { config }
    }
}

#[async_trait::async_trait]
impl PermissionChecker for Live {
    async fn check_permission(&self, perm: Permission, cmd: Option<&str>) -> Result<bool, String> {
        let config = self.get_policy(perm);

        match config {
            Policy::Once => Ok(false),
            Policy::Always(whitelist) => match whitelist {
                forge_domain::Whitelisted::All => Ok(true),
                forge_domain::Whitelisted::Some(commands) => {
                    if let Some(cmd) = cmd {
                        Ok(commands.iter().any(|c| c.0.starts_with(cmd)))
                    } else {
                        Ok(false)
                    }
                }
            },
        }
    }
}

impl PermissionService for Live {
    fn get_policy(&self, permission: Permission) -> &Policy {
        self.config.policies.get(&permission).unwrap_or({
            // Default to most restrictive policy
            &Policy::Once
        })
    }
}

impl Service {
    pub fn permission_service() -> Arc<dyn PermissionService> {
        let config_path = std::env::var("FORGE_CONFIG")
            .map(PathBuf::from)
            .unwrap_or_else(|_| "config.yml".into());

        let loader = crate::permission::PermissionLoader::new(config_path);
        let config = loader.load().unwrap_or_default();

        Arc::new(Live::new(config))
    }
}

#[cfg(test)]
pub mod tests {
    use std::fs;

    use forge_domain::Whitelisted;
    use tempfile::TempDir;

    use super::*;

    pub struct TestPermissionService {
        config: PermissionConfig,
    }

    impl TestPermissionService {
        pub fn new(config: PermissionConfig) -> Self {
            Self { config }
        }

        pub fn default() -> Self {
            Self { config: PermissionConfig::default() }
        }
    }
    #[async_trait::async_trait]
    impl PermissionChecker for TestPermissionService {
        async fn check_permission(
            &self,
            perm: Permission,
            cmd: Option<&str>,
        ) -> Result<bool, String> {
            let config = self.get_policy(perm);
            match config {
                Policy::Once => Ok(false),
                Policy::Always(whitelist) => match whitelist {
                    Whitelisted::All => Ok(true),
                    Whitelisted::Some(commands) => {
                        if let Some(cmd) = cmd {
                            Ok(commands.iter().any(|c| c.0.starts_with(cmd)))
                        } else {
                            Ok(false)
                        }
                    }
                },
            }
        }
    }

    impl PermissionService for TestPermissionService {
        fn get_policy(&self, permission: Permission) -> &Policy {
            self.config
                .policies
                .get(&permission)
                .unwrap_or(&Policy::Once)
        }
    }

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
        std::env::set_var("FORGE_CONFIG", config_path);

        let service = Service::permission_service();
        assert!(matches!(service.get_policy(Permission::Read), Policy::Once));
    }

    #[test]
    fn test_load_full_config() {
        let yaml_content = r#"
            read: "Always: all"
            write: always
            execute:
              Always:
                Some: ["ls", "git status"]
        "#;
        let (_temp_dir, config_path) = setup_test_config(yaml_content);
        std::env::set_var("FORGE_CONFIG", config_path);

        let service = Service::permission_service();

        assert!(matches!(
            service.get_policy(Permission::Read),
            Policy::Always(Whitelisted::All)
        ));

        if let Policy::Always(Whitelisted::Some(commands)) = service.get_policy(Permission::Execute)
        {
            assert_eq!(commands.len(), 2);
            assert_eq!(commands[0].0, "ls");
            assert_eq!(commands[1].0, "git status");
        } else {
            panic!("Expected Some whitelist for execute permission");
        }
    }

    #[test]
    fn test_mixed_format() {
        let yaml_content = r#"
            read: "Always: all"
            write: 
              Always: "all"
            execute:
              Always:
                Some: ["ls"]
        "#;
        let (_temp_dir, config_path) = setup_test_config(yaml_content);
        std::env::set_var("FORGE_CONFIG", config_path);

        let service = Service::permission_service();

        assert!(matches!(
            service.get_policy(Permission::Read),
            Policy::Always(Whitelisted::All)
        ));
        assert!(matches!(
            service.get_policy(Permission::Write),
            Policy::Always(Whitelisted::All)
        ));

        if let Policy::Always(Whitelisted::Some(commands)) = service.get_policy(Permission::Execute)
        {
            assert_eq!(commands.len(), 1);
            assert_eq!(commands[0].0, "ls");
        } else {
            panic!("Expected Some whitelist for execute permission");
        }
    }

    #[test]
    fn test_default_policy_for_missing_permission() {
        let yaml_content = r#"
            read: once
            # write permission missing
            execute: once
        "#;
        let (_temp_dir, config_path) = setup_test_config(yaml_content);
        std::env::set_var("FORGE_CONFIG", config_path);

        let service = Service::permission_service();
        assert!(matches!(
            service.get_policy(Permission::Write),
            Policy::Once
        ));
    }
}
