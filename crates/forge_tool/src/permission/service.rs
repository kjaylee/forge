use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use forge_domain::{Permission, PermissionConfig, PermissionResult, Policy};
use tokio::sync::RwLock;

use crate::permission::path_validator::PathValidator;

/// Live permission service implementation
pub struct LivePermissionService {
    config: PermissionConfig,
    path_validator: PathValidator,
    session_state: Arc<RwLock<HashMap<(PathBuf, Permission), bool>>>,
}

impl LivePermissionService {
    /// Create new service instance
    pub fn new() -> Self {
        let config = PermissionConfig::default();
        let cwd = std::env::current_dir().unwrap_or_default();
        Self {
            config,
            path_validator: PathValidator::new(cwd),
            session_state: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Check if an operation is allowed
    pub async fn check_permission(&self, path: &Path, perm: Permission) -> PermissionResult<bool> {
        // First validate the path
        self.path_validator.validate_path(path, None).await?;

        // Check deny patterns
        if self.is_denied(path) {
            return Ok(false);
        }

        // Check session state
        let state = self.session_state.read().await;
        if let Some(&allowed) = state.get(&(path.to_path_buf(), perm)) {
            return Ok(allowed);
        }

        // Check configured policy
        let policy = self
            .config
            .permissions
            .get(&perm)
            .unwrap_or(&self.config.default_policy);

        Ok(matches!(policy, Policy::Always))
    }

    /// Update permission state
    pub async fn update_permission(
        &self,
        path: &Path,
        perm: Permission,
        allowed: bool,
    ) -> PermissionResult<()> {
        let mut state = self.session_state.write().await;
        state.insert((path.to_path_buf(), perm), allowed);
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

impl Default for LivePermissionService {
    fn default() -> Self {
        Self::new()
    }
}
