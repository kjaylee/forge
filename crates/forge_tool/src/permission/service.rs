use std::path::PathBuf;
use std::sync::RwLock;
use std::collections::HashMap;

use async_trait::async_trait;
use forge_domain::{Permission, PermissionError, PermissionResult, PermissionService, PermissionState};

pub struct LivePermissionService {
    permissions: RwLock<HashMap<(String, String), Permission>>,
}

impl LivePermissionService {
    pub fn new() -> Self {
        Self {
            permissions: RwLock::new(HashMap::new()),
        }
    }
}

#[async_trait]
impl PermissionService for LivePermissionService {
    async fn check_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<Permission> {
        let key = (path.to_string_lossy().to_string(), tool_name.clone());
        let permissions = self.permissions.read().unwrap();
        permissions
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
        let permission = Permission::new(state, path.clone(), tool_name.clone());
        let key = (path.to_string_lossy().to_string(), tool_name);
        let mut permissions = self.permissions.write().unwrap();
        permissions.insert(key, permission.clone());
        Ok(permission)
    }

    async fn revoke_permission(
        &self,
        path: PathBuf,
        tool_name: String,
    ) -> PermissionResult<()> {
        let key = (path.to_string_lossy().to_string(), tool_name);
        let mut permissions = self.permissions.write().unwrap();
        if permissions.remove(&key).is_some() {
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

impl Default for LivePermissionService {
    fn default() -> Self {
        Self::new()
    }
}