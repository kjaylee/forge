use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tokio::sync::RwLock;
use glob::glob;

use super::{Permission, Policy, PermissionConfig, PermissionResult, PermissionError};
use forge_walker::Walker;

/// Simple permission service for managing file system access
pub struct PermissionService {
    config: PermissionConfig,
    path_validator: PathValidator,
    session_state: Arc<RwLock<HashMap<(PathBuf, Permission), bool>>>,
}

impl PermissionService {
    /// Create a new permission service
    pub fn new(config: PermissionConfig, cwd: PathBuf) -> Self {
        Self {
            config,
            path_validator: PathValidator::new(cwd),
            session_state: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Check if an operation is allowed
    pub async fn check_permission(&self, path: &Path, permission: Permission) -> PermissionResult<bool> {
        // First validate the path
        self.validate_path(path).await?;

        // Check deny patterns
        if self.is_denied(path) {
            return Ok(false);
        }

        // Check session state
        let state = self.session_state.read().await;
        if let Some(&allowed) = state.get(&(path.to_path_buf(), permission.clone())) {
            return Ok(allowed);
        }

        // Check configured policy
        let policy = self.config.permissions
            .get(&permission)
            .unwrap_or(&self.config.default_policy);

        Ok(matches!(policy, Policy::Always))
    }

    /// Update permission state
    pub async fn update_permission(&self, path: &Path, permission: Permission, allowed: bool) -> PermissionResult<()> {
        let mut state = self.session_state.write().await;
        state.insert((path.to_path_buf(), permission), allowed);
        Ok(())
    }

    /// Validate if a path is accessible
    pub async fn validate_path(&self, path: &Path) -> PermissionResult<PathBuf> {
        self.path_validator.validate_path(path, None).await
    }

    /// Check if path matches any deny patterns
    fn is_denied(&self, path: &Path) -> bool {
        let path_str = path.to_string_lossy();
        self.config.deny_patterns.iter().any(|pattern| {
            glob(pattern)
                .map(|paths| paths.any(|p| p.map(|p| p.to_string_lossy() == path_str).unwrap_or(false)))
                .unwrap_or(false)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_permissions() {
        let mut config = PermissionConfig::default();
        config.permissions.insert(Permission::Read, Policy::Always);
        
        let cwd = std::env::current_dir().unwrap();
        let service = PermissionService::new(config, cwd.clone());

        assert!(service.check_permission(&cwd.join("Cargo.toml"), Permission::Read).await.unwrap());
        assert!(!service.check_permission(&cwd.join("Cargo.toml"), Permission::Write).await.unwrap());
    }

    #[tokio::test]
    async fn test_session_state() {
        let config = PermissionConfig::default();
        let cwd = std::env::current_dir().unwrap();
        let service = PermissionService::new(config, cwd.clone());
        let test_path = cwd.join("test.txt");

        service.update_permission(&test_path, Permission::Write, true).await.unwrap();
        assert!(service.check_permission(&test_path, Permission::Write).await.unwrap());
    }

    #[tokio::test]
    async fn test_deny_patterns() {
        let mut config = PermissionConfig::default();
        config.deny_patterns.push("**/secrets/**".to_string());
        
        let cwd = std::env::current_dir().unwrap();
        let service = PermissionService::new(config, cwd.clone());
        let secret_path = cwd.join("secrets").join("test.txt");

        assert!(!service.check_permission(&secret_path, Permission::Read).await.unwrap());
    }
}
