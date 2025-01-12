use async_trait::async_trait;

use super::{Permission, PermissionResult, PermissionRequest};

/// Service for managing permissions
#[async_trait]
pub trait PermissionService: Send + Sync {
    /// Check if an operation is allowed for the given path and tool.
    async fn check_permission(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<bool>;

    /// Grant a new permission
    async fn grant_permission(
        &self,
        permission: Permission,
    ) -> PermissionResult<()>;

    /// Revoke an existing permission
    async fn revoke_permission(
        &self,
        request: &PermissionRequest
    ) -> PermissionResult<()>;

    /// Validate path access with context
    async fn validate_path_access(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<()>;

    /// Check directory access
    async fn check_directory_access(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<()>;
}

/// Test implementation of PermissionService
#[cfg(test)]
pub struct TestPermissionService {
    allow_all: bool,
}

#[cfg(test)]
impl Default for TestPermissionService {
    fn default() -> Self {
        Self::new()
    }
}
#[cfg(test)]
impl TestPermissionService {
    pub fn new() -> Self {
        Self { allow_all: false }
    }

    pub fn allow_all() -> Self {
        Self { allow_all: true }
    }
}

#[cfg(test)]
#[async_trait]
impl PermissionService for TestPermissionService {
    async fn check_permission(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<bool> {
        if self.allow_all {
            Ok(true)
        } else {
            Err(super::PermissionError::SystemDenied(request.path().to_path_buf()))
        }
    }

    async fn grant_permission(
        &self,
        _permission: Permission,
    ) -> PermissionResult<()> {
        Ok(())
    }

    async fn revoke_permission(
        &self,
        _request: &PermissionRequest
    ) -> PermissionResult<()> {
        Ok(())
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
