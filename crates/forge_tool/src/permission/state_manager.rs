//! Thread-safe state management for permissions.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use forge_domain::{Permission, PermissionResult, PermissionState};
use tokio::sync::RwLock;

/// Key type for permission lookups.
type PermissionKey = (String, String);

/// Manages the in-memory state of permissions.
#[derive(Debug, Clone)]
pub struct StateManager {
    permissions: Arc<RwLock<HashMap<PermissionKey, Permission>>>,
}

impl StateManager {
    /// Creates a new state manager.
    pub fn new() -> Self {
        Self {
            permissions: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Creates a key for permission lookup.
    fn create_key(path: &PathBuf, tool_name: &str) -> PermissionKey {
        (path.to_string_lossy().to_string(), tool_name.to_string())
    }

    /// Stores a new permission.
    pub async fn store_permission(&self, permission: Permission) -> PermissionResult<()> {
        let key = Self::create_key(&permission.path, &permission.tool_name);
        let mut permissions = self.permissions.write().await;
        permissions.insert(key, permission);
        Ok(())
    }

    /// Gets a permission if it exists and is valid.
    pub async fn get_permission(&self, path: &PathBuf, tool_name: &str) -> PermissionResult<Option<Permission>> {
        let key = Self::create_key(path, tool_name);
        let mut permissions = self.permissions.write().await;
        
        if let Some(permission) = permissions.get_mut(&key) {
            if permission.is_valid() {
                let mut cloned = permission.clone();
                
                // For AllowOnce, deactivate after retrieval
                if permission.state == PermissionState::AllowOnce {
                    permission.deactivate();
                }
                
                return Ok(Some(cloned));
            }
        }
        
        Ok(None)
    }

    /// Revokes a permission if it exists.
    pub async fn revoke_permission(&self, path: &PathBuf, tool_name: &str) -> PermissionResult<()> {
        let key = Self::create_key(path, tool_name);
        let mut permissions = self.permissions.write().await;
        
        if let Some(permission) = permissions.get_mut(&key) {
            permission.deactivate();
        }
        
        Ok(())
    }

    /// Clears all permissions.
    pub async fn clear(&self) -> PermissionResult<()> {
        let mut permissions = self.permissions.write().await;
        permissions.clear();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_permission_lifecycle() {
        let manager = StateManager::new();
        let path = PathBuf::from("/test/path");
        let tool_name = "fs_read".to_string();

        // Test storing and retrieving permission
        let permission = Permission::new(
            PermissionState::AllowSession,
            path.clone(),
            tool_name.clone(),
        );
        manager.store_permission(permission).await.unwrap();

        let retrieved = manager.get_permission(&path, &tool_name).await.unwrap();
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().state, PermissionState::AllowSession);

        // Test revoking permission
        manager.revoke_permission(&path, &tool_name).await.unwrap();
        let retrieved = manager.get_permission(&path, &tool_name).await.unwrap();
        assert!(retrieved.is_none());
    }

    #[tokio::test]
    async fn test_allow_once_behavior() {
        let manager = StateManager::new();
        let path = PathBuf::from("/test/path");
        let tool_name = "fs_read".to_string();

        // Store AllowOnce permission
        let permission = Permission::new(
            PermissionState::AllowOnce,
            path.clone(),
            tool_name.clone(),
        );
        manager.store_permission(permission).await.unwrap();

        // First retrieval should succeed
        let retrieved = manager.get_permission(&path, &tool_name).await.unwrap();
        assert!(retrieved.is_some());

        // Second retrieval should fail (permission deactivated)
        let retrieved = manager.get_permission(&path, &tool_name).await.unwrap();
        assert!(retrieved.is_none());
    }

    #[tokio::test]
    async fn test_clear_permissions() {
        let manager = StateManager::new();
        let path = PathBuf::from("/test/path");
        let tool_name = "fs_read".to_string();

        // Store a permission
        let permission = Permission::new(
            PermissionState::AllowSession,
            path.clone(),
            tool_name.clone(),
        );
        manager.store_permission(permission).await.unwrap();

        // Clear all permissions
        manager.clear().await.unwrap();

        // Verify permission is gone
        let retrieved = manager.get_permission(&path, &tool_name).await.unwrap();
        assert!(retrieved.is_none());
    }
}