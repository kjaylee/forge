use crate::permission::storage::{SessionStorage, ConfigStorage};
use forge_domain::{PermissionRequest, PermissionResult, PermissionState, Permission, PermissionStorage};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct PermissionManager {
    session: SessionStorage,
    config: ConfigStorage,
    cache: Arc<RwLock<HashMap<(String, String), Permission>>>,
}

impl PermissionManager {
    pub fn new(session: SessionStorage, config: ConfigStorage) -> Self {
        Self { session, config, cache: Arc::new(RwLock::new(HashMap::new())) }
    }

    pub async fn check_permission(&self, request: &PermissionRequest) -> PermissionResult<PermissionState> {
        let key = (request.path().to_string_lossy().to_string(), request.tool_name().to_string());

        {
            let cache = self.cache.read().await;
            if let Some(permission) = cache.get(&key) {
                return Ok(permission.state.clone());
            }
        }

        let session_permission = self.session.load(request.path(), request.tool_name()).await?;
        if let Some(permission) = session_permission {
            let mut cache = self.cache.write().await;
            cache.insert(key, permission.clone());
            return Ok(permission.state);
        }

        let config_permission = self.config.load(request.path(), request.tool_name()).await?;
        if let Some(permission) = config_permission {
            let mut cache = self.cache.write().await;
             cache.insert(key, permission.clone());
            return Ok(permission.state);
        }

        Ok(PermissionState::Reject)
    }
    #[cfg(test)]
    pub async fn handle_request(&self, request: &PermissionRequest) -> PermissionResult<bool> {
        let permission_state = self.check_permission(request).await?;
        match permission_state {
            PermissionState::Allow => Ok(true),
            PermissionState::AllowSession => {
                let permission = Permission::new(
                    PermissionState::AllowSession,
                    request.path().to_path_buf(),
                    request.tool_name().to_string(),
                );
                self.session.save(permission).await?;
                Ok(true)
            },
            PermissionState::AllowForever => {
                 let permission = Permission::new(
                    PermissionState::AllowForever,
                    request.path().to_path_buf(),
                    request.tool_name().to_string(),
                );
                self.config.save(permission).await?;
                Ok(true)
            },
            PermissionState::Reject => Ok(false),
        }
    }
}
