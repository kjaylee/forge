use forge_domain::{Permission, PermissionConfig, PermissionResult, Policy, Whitelisted};

/// Live permission service implementation
pub struct LivePermissionService {
    config: PermissionConfig,
}

impl LivePermissionService {
    /// Create new service instance with provided config
    pub fn new(config: PermissionConfig) -> Self {
        Self { config }
    }

    /// Check if an operation is allowed based on policy
    pub async fn check_permission(
        &self,
        perm: Permission,
        cmd: Option<&str>,
    ) -> PermissionResult<bool> {
        match self.config.policies.get(&perm) {
            Some(Policy::Once) => Ok(false), // Always ask for permission
            Some(Policy::Always(whitelist)) => match (perm, whitelist, cmd) {
                // For Execute permission, check command against whitelist
                (Permission::Execute, _, None) => Ok(false), // Execute needs a command
                (Permission::Execute, Whitelisted::All, _) => Ok(true),
                (Permission::Execute, Whitelisted::Some(commands), Some(cmd)) => {
                    Ok(commands.iter().any(|c| cmd.contains(&c.0)))
                }
                // For Read/Write, any Always policy grants permission
                (_, _, _) => Ok(true),
            },
            None => Ok(false), // If no policy exists, deny by default
        }
    }
}

impl Default for LivePermissionService {
    fn default() -> Self {
        Self::new(PermissionConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use forge_domain::Command;

    use super::*;

    #[tokio::test]
    async fn test_once_permissions() {
        let service = LivePermissionService::default();

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
        let mut policies = HashMap::new();
        policies.insert(Permission::Read, Policy::Once);
        policies.insert(Permission::Write, Policy::Once);
        policies.insert(
            Permission::Execute,
            Policy::Always(Whitelisted::Some(vec![
                Command("ls".to_string()),
                Command("git".to_string()),
            ])),
        );

        let config = PermissionConfig { policies };
        let service = LivePermissionService::new(config);

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
        let mut policies = HashMap::new();
        policies.insert(Permission::Read, Policy::Always(Whitelisted::All));
        policies.insert(Permission::Write, Policy::Once);
        policies.insert(Permission::Execute, Policy::Once);

        let config = PermissionConfig { policies };
        let service = LivePermissionService::new(config);

        let result = service.check_permission(Permission::Read, None).await;
        assert!(
            matches!(result, Ok(true)),
            "Always policy should allow read"
        );
    }
}
