use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use forge_domain::{Permission, PermissionConfig, PermissionResult, Policy};
use tokio::sync::RwLock;

use crate::permission::path_validator::PathValidator;

/// Live permission service implementation
pub struct LivePermissionService {
    config: PermissionConfig,
    path_validator: PathValidator,
    session_state: Arc<RwLock<HashMap<Permission, bool>>>,
}

impl LivePermissionService {
    /// Create new service instance with automatic config loading
    pub async fn new() -> Self {
        let config = forge_domain::load_or_default().await;
        let cwd = std::env::current_dir().unwrap_or_default();
        Self {
            config,
            path_validator: PathValidator::new(cwd),
            session_state: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Create new service instance with default configuration without loading
    pub fn with_defaults() -> Self {
        let config = PermissionConfig::default();
        let cwd = std::env::current_dir().unwrap_or_default();
        Self {
            config,
            path_validator: PathValidator::new(cwd),
            session_state: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Create new service instance with configuration from file
    pub async fn from_file<P: AsRef<Path>>(
        config_path: P,
    ) -> Result<Self, forge_domain::LoadError> {
        let config = forge_domain::load_config(config_path).await?;
        let cwd = std::env::current_dir().unwrap_or_default();
        Ok(Self {
            config,
            path_validator: PathValidator::new(cwd),
            session_state: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    /// Update configuration
    pub fn set_config(&mut self, config: PermissionConfig) {
        self.config = config;
    }

    /// Check if an operation is allowed based on policy and session state
    pub async fn check_permission(&self, path: &Path, perm: Permission) -> PermissionResult<bool> {
        let validated_path = self.path_validator.validate_path(path, None).await?;

        // Check deny patterns first
        if self.is_denied(&validated_path) {
            return Ok(false);
        }

        // For paths outside CWD, always require permission
        if !validated_path.starts_with(self.path_validator.cwd()) {
            return Ok(false);
        }

        // For paths within CWD, use policy-based logic
        let policy = self
            .config
            .permissions
            .get(&perm)
            .unwrap_or(&self.config.default_policy);

        match policy {
            Policy::Always => Ok(true),
            Policy::Session => {
                let state = self.session_state.read().await;
                match state.get(&perm) {
                    Some(&allowed) => Ok(allowed),
                    None => Ok(false), // Need to ask
                }
            }
            Policy::Once => Ok(false), // Always ask
        }
    }

    /// Update permission state in session
    pub async fn update_permission(
        &self,
        path: &Path,
        perm: Permission,
        allowed: bool,
    ) -> PermissionResult<()> {
        let validated_path = self.path_validator.validate_path(path, None).await?;

        if validated_path.starts_with(self.path_validator.cwd()) {
            let policy = self
                .config
                .permissions
                .get(&perm)
                .unwrap_or(&self.config.default_policy);

            if matches!(policy, Policy::Session) {
                let mut state = self.session_state.write().await;
                state.insert(perm, allowed);
            }
        }
        // Do not store any state for paths outside CWD

        Ok(())
    }

    /// Check if path matches deny patterns
    fn is_denied(&self, path: &Path) -> bool {
        let path_str = path.to_string_lossy();
        self.config.deny_patterns.iter().any(|pattern| {
            glob::glob(pattern)
                .map(|mut paths| {
                    paths.any(|p| p.map(|p| p.to_string_lossy() == path_str).unwrap_or(false))
                })
                .unwrap_or(false)
        })
    }
}

#[async_trait::async_trait]
impl Default for LivePermissionService {
    fn default() -> Self {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        runtime.block_on(Self::new())
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use forge_domain::{Permission, PermissionConfig, Policy};
    use tempfile::TempDir;

    use super::*;

    impl LivePermissionService {
        pub fn new_with_base(base_path: PathBuf) -> Self {
            let config = PermissionConfig::default();
            Self {
                config,
                path_validator: PathValidator::new(base_path),
                session_state: Arc::new(RwLock::new(HashMap::new())),
            }
        }
    }

    async fn setup_test_dir() -> (TempDir, PathBuf) {
        let dir = TempDir::new().unwrap();
        std::fs::create_dir_all(dir.path()).unwrap();
        let path = dir.path().canonicalize().unwrap();
        (dir, path)
    }

    async fn setup_nested_dir(base_path: &Path, path: &str) -> PathBuf {
        let full_path = base_path.join(path);
        std::fs::create_dir_all(&full_path).unwrap();
        full_path
    }

    #[tokio::test]
    async fn test_session_permission_is_remembered() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let test_file = base_path.join("test.txt");
        std::fs::write(&test_file, "test").unwrap();

        // Create service with Session policy
        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        config
            .permissions
            .insert(Permission::Write, Policy::Session);
        service.set_config(config);

        // First check should require permission
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "First check should require permission"
        );

        // Grant permission
        service
            .update_permission(&test_file, Permission::Write, true)
            .await
            .unwrap();

        // Second check should pass automatically
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(matches!(result, Ok(true)), "Second check should be granted");
    }

    #[tokio::test]
    async fn test_once_permission_not_remembered() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let test_file = base_path.join("test.txt");
        std::fs::write(&test_file, "test").unwrap();

        // Create service with Once policy
        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        config.permissions.insert(Permission::Write, Policy::Once);
        service.set_config(config);

        // First check should require permission
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "First check should require permission"
        );

        // Grant permission
        service
            .update_permission(&test_file, Permission::Write, true)
            .await
            .unwrap();

        // Second check should still require permission
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Second check should still require permission"
        );
    }

    #[tokio::test]
    async fn test_always_permission_never_asks() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let test_file = base_path.join("test.txt");
        std::fs::write(&test_file, "test").unwrap();

        // Create service with Always policy
        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        config.permissions.insert(Permission::Write, Policy::Always);
        service.set_config(config);

        // Should always be granted without asking
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(
            matches!(result, Ok(true)),
            "Should be granted without asking"
        );
    }

    #[tokio::test]
    async fn test_deny_pattern_blocks_permission() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let node_modules = setup_nested_dir(&base_path, "node_modules").await;
        let test_file = node_modules.join("test.txt");
        std::fs::write(&test_file, "test").unwrap();

        // Create service with deny pattern
        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        config.deny_patterns.push("**/node_modules/**".to_string());
        service.set_config(config);

        // Should be denied regardless of policy
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Should be denied due to deny pattern"
        );
    }

    #[tokio::test]
    async fn test_session_permission_multiple_paths() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let dir1 = base_path.join("dir1");
        let dir2 = base_path.join("dir2");
        std::fs::create_dir_all(&dir1).unwrap();
        std::fs::create_dir_all(&dir2).unwrap();

        let file1 = dir1.join("test1.txt");
        let file2 = dir2.join("test2.txt");
        std::fs::write(&file1, "test1").unwrap();
        std::fs::write(&file2, "test2").unwrap();

        // Create service with Session policy
        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        config
            .permissions
            .insert(Permission::Write, Policy::Session);
        service.set_config(config);

        // Initially no files should be allowed
        let result = service.check_permission(&file1, Permission::Write).await;
        assert!(
            matches!(result, Ok(false)),
            "Should require permission initially"
        );

        // After granting permission, all CWD files should be allowed
        service
            .update_permission(&file1, Permission::Write, true)
            .await
            .unwrap();

        // All files in CWD should now be allowed
        let result = service.check_permission(&file1, Permission::Write).await;
        assert!(matches!(result, Ok(true)), "File1 should be allowed");
        let result = service.check_permission(&file2, Permission::Write).await;
        assert!(matches!(result, Ok(true)), "File2 should be allowed");

        // Files in CWD should still be allowed
        let new_file = dir1.parent().unwrap().join("test3.txt");
        let result = service.check_permission(&new_file, Permission::Write).await;
        assert!(
            matches!(result, Ok(true)),
            "New files in CWD should be allowed"
        );
    }

    #[tokio::test]
    async fn test_multiple_permissions_same_path() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let test_file = base_path.join("test.txt");
        std::fs::write(&test_file, "test").unwrap();

        // Create service with different policies for different permissions
        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        config.permissions.insert(Permission::Read, Policy::Always);
        config
            .permissions
            .insert(Permission::Write, Policy::Session);
        service.set_config(config);

        // Read should be allowed immediately
        let result = service.check_permission(&test_file, Permission::Read).await;
        assert!(
            matches!(result, Ok(true)),
            "Read should be allowed immediately"
        );

        // Write should require permission
        let result = service
            .check_permission(&test_file, Permission::Write)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Write should require permission"
        );
    }

    #[tokio::test]
    async fn test_outside_cwd_always_requires_permission() {
        let (_temp_dir, base_path) = setup_test_dir().await;
        let outside_path = base_path.parent().unwrap().join("outside.txt");
        std::fs::write(&outside_path, "test").unwrap();

        let mut service = LivePermissionService::new_with_base(base_path.clone());
        let mut config = PermissionConfig::default();
        // Even with Always policy, outside CWD should require permission
        config.permissions.insert(Permission::Read, Policy::Always);
        service.set_config(config);

        // Should require permission for all external paths
        let result = service
            .check_permission(&outside_path, Permission::Read)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Outside CWD should require permission even with Always policy"
        );

        // Should still require permission even after granting
        service
            .update_permission(&outside_path, Permission::Read, true)
            .await
            .unwrap();
        let result = service
            .check_permission(&outside_path, Permission::Read)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Outside CWD should always require permission"
        );

        // Different path should also require permission
        let other_outside = outside_path.with_file_name("other.txt");
        let result = service
            .check_permission(&other_outside, Permission::Read)
            .await;
        assert!(
            matches!(result, Ok(false)),
            "Different outside path should require permission"
        );
    }
}
