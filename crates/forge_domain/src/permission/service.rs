//! Service trait for the permission system.

use std::path::PathBuf;
use std::sync::Arc;
use std::collections::HashMap;

use async_trait::async_trait;
use tokio::sync::RwLock;

use crate::tool_name::ToolName;
use super::{
    ConfigLoader, Permission, PermissionConfig, PermissionError,
    PermissionResult, PermissionState,
};

/// Service for managing file system permissions.
#[async_trait]
pub trait PermissionService: Send + Sync {
    /// Check if an operation is allowed for the given path and tool.
    async fn check_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission>;

    /// Grant a new permission.
    async fn grant_permission(
        &self,
        state: PermissionState,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission>;

    /// Revoke an existing permission.
    async fn revoke_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<()>;

    /// Validate if a path is accessible based on current permissions.
    async fn validate_path_access(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<()>;

    /// Check directory access with optional depth limit.
    async fn check_directory_access(
        &self,
        path: PathBuf,
        tool_name: String,
        max_depth: Option<usize>,
    ) -> PermissionResult<()>;
}

/// Test implementation of PermissionService
pub struct TestPermissionService {
    permissions: HashMap<(String, String), Permission>,
}

impl TestPermissionService {
    pub fn new() -> Self {
        Self {
            permissions: HashMap::new(),
        }
    }

    pub fn with_permission(mut self, permission: Permission) -> Self {
        let key = (
            permission.path.to_string_lossy().to_string(),
            permission.tool_name.clone(),
        );
        self.permissions.insert(key, permission);
        self
    }
}

#[async_trait]
impl PermissionService for TestPermissionService {
    async fn check_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission> {
        let key = (path.to_string_lossy().to_string(), tool_name.clone());
        self.permissions
            .get(&key)
            .cloned()
            .ok_or_else(|| PermissionError::AccessDenied(path))
    }

    async fn grant_permission(
        &self,
        state: PermissionState,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission> {
        Ok(Permission::new(state, path, tool_name))
    }

    async fn revoke_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<()> {
        let key = (path.to_string_lossy().to_string(), tool_name);
        if self.permissions.contains_key(&key) {
            Ok(())
        } else {
            Err(PermissionError::AccessDenied(path))
        }
    }

    async fn validate_path_access(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<()> {
        self.check_permission(path.clone(), tool_name)
            .await
            .map(|_| ())
    }

    async fn check_directory_access(
        &self,
        path: PathBuf,
        tool_name: String,
        _max_depth: Option<usize>,
    ) -> PermissionResult<()> {
        self.validate_path_access(path, tool_name).await
    }
}

/// Live implementation
struct Live {
    config: Arc<RwLock<PermissionConfig>>,
    config_loader: ConfigLoader,
}

impl Live {
    fn new() -> PermissionResult<Self> {
        let config_loader = ConfigLoader::new()?;
        let config = config_loader.load()?;
        
        Ok(Self {
            config: Arc::new(RwLock::new(config)),
            config_loader,
        })
    }

    fn with_config<P: AsRef<std::path::Path>>(path: P) -> PermissionResult<Self> {
        let config_loader = ConfigLoader::with_path(path);
        let config = config_loader.load()?;
        
        Ok(Self {
            config: Arc::new(RwLock::new(config)),
            config_loader,
        })
    }

    async fn save_config(&self) -> PermissionResult<()> {
        let config = self.config.read().await;
        self.config_loader.save(&config)
    }

    async fn reload_config(&self) -> PermissionResult<()> {
        let new_config = self.config_loader.load()?;
        let mut config = self.config.write().await;
        *config = new_config;
        Ok(())
    }
}

#[async_trait]
impl PermissionService for Live {
    async fn check_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission> {
        let config = self.config.read().await;
        let tool_name = ToolName::new(&tool_name);
        
        let tool_config = config.tools
            .get(&tool_name)
            .ok_or_else(|| PermissionError::AccessDenied(path.clone()))?;

        for dir_config in &tool_config.directories {
            if path.starts_with(&dir_config.path) {
                if let Some(max_depth) = dir_config.max_depth {
                    let depth = path.components().count().saturating_sub(
                        dir_config.path.components().count()
                    );
                    if depth > max_depth {
                        return Err(PermissionError::AccessDenied(path));
                    }
                }
                
                return Ok(Permission::new(
                    PermissionState::AllowDirectory,
                    path,
                    tool_name.as_str().to_string(),
                ));
            }
        }

        if tool_config.require_approval_outside_cwd {
            Err(PermissionError::OutsideAllowedDirectory(path))
        } else {
            Ok(Permission::new(
                tool_config.default_state,
                path,
                tool_name.as_str().to_string(),
            ))
        }
    }

    async fn grant_permission(
        &self,
        state: PermissionState,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission> {
        Ok(Permission::new(state, path, tool_name))
    }

    async fn revoke_permission(
        &self,
        _path: PathBuf,
        _tool_name: String,
    ) -> PermissionResult<()> {
        Ok(())
    }

    async fn validate_path_access(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<()> {
        self.check_permission(path, tool_name)
            .await
            .map(|_| ())
    }

    async fn check_directory_access(
        &self,
        path: PathBuf,
        tool_name: String,
        max_depth: Option<usize>,
    ) -> PermissionResult<()> {
        let config = self.config.read().await;
        let tool_name = ToolName::new(&tool_name);
        
        let tool_config = config.tools
            .get(&tool_name)
            .ok_or_else(|| PermissionError::AccessDenied(path.clone()))?;

        for dir_config in &tool_config.directories {
            if path.starts_with(&dir_config.path) {
                let effective_max_depth = match (max_depth, dir_config.max_depth) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (None, None) => None,
                };

                if let Some(max_depth) = effective_max_depth {
                    let depth = path.components().count().saturating_sub(
                        dir_config.path.components().count()
                    );
                    if depth > max_depth {
                        return Err(PermissionError::AccessDenied(path));
                    }
                }
                
                return Ok(());
            }
        }

        if tool_config.require_approval_outside_cwd {
            Err(PermissionError::OutsideAllowedDirectory(path))
        } else {
            Ok(())
        }
    }
}

impl crate::Service {
    pub fn permission_service() -> PermissionResult<impl PermissionService> {
        Live::new()
    }

    pub fn permission_service_with_config<P: AsRef<std::path::Path>>(
        path: P
    ) -> PermissionResult<impl PermissionService> {
        Live::with_config(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[tokio::test]
    async fn test_live_service() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("test_permissions.yml");

        let config = PermissionConfig::default();
        let config_loader = ConfigLoader::with_path(&config_path);
        config_loader.save(&config).unwrap();

        let service = Live::with_config(&config_path).unwrap();

        let result = service
            .check_permission(
                PathBuf::from("/test/path"),
                "fs_read".to_string(),
            )
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_service_reload() {
        let temp_dir = TempDir::new().unwrap();
        let config_path = temp_dir.path().join("test_permissions.yml");

        let mut config = PermissionConfig::default();
        let config_loader = ConfigLoader::with_path(&config_path);
        config_loader.save(&config).unwrap();

        let service = Live::with_config(&config_path).unwrap();

        config.global.max_depth = 20;
        config_loader.save(&config).unwrap();

        service.reload_config().await.unwrap();

        let loaded_config = service.config.read().await;
        assert_eq!(loaded_config.global.max_depth, 20);
    }
}