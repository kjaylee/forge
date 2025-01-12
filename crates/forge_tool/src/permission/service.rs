use tokio::sync::RwLock;
use std::collections::HashMap;

use async_trait::async_trait;
use forge_domain::{Permission, PermissionError, PermissionResult, PermissionService, PermissionRequest};

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
        request: &PermissionRequest,
    ) -> PermissionResult<bool> {
        let key = (request.path().to_string_lossy().to_string(), request.tool_name().to_string());
        let permissions = self.permissions.read().await;
        if permissions.contains_key(&key) {
            Ok(true)
        } else {
            Err(PermissionError::SystemDenied(request.path().to_path_buf()))
        }
    }

    async fn grant_permission(
        &self,
        permission: Permission,
    ) -> PermissionResult<()> {
        let key = (
            permission.path().to_string_lossy().to_string(),
            permission.tool_name().to_string(),
        );
        let mut permissions = self.permissions.write().await;
        permissions.insert(key, permission);
        Ok(())
    }

    async fn revoke_permission(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<()> {
        let key = (request.path().to_string_lossy().to_string(), request.tool_name().to_string());
        let mut permissions = self.permissions.write().await;
        if permissions.remove(&key).is_some() {
            Ok(())
        } else {
            Err(PermissionError::SystemDenied(request.path().to_path_buf()))
        }
    }

    async fn validate_path_access(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<()> {
        self.check_permission(request)
            .await
            .map(|_| ())
    }

    async fn check_directory_access(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<()> {
        self.validate_path_access(request).await
    }
}

impl Default for LivePermissionService {
    fn default() -> Self {
        Self::new()
    }
}
