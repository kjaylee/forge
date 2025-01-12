use std::time::Duration;
use async_trait::async_trait;
use crate::permission::{PermissionRequest, PermissionResult, PermissionState};

/// Trait for handling permission interaction with users.
/// Implementations should provide a way to request permission
/// decisions from users through different interfaces (CLI, GUI, etc.)
#[async_trait]
pub trait PermissionInteraction: Send + Sync {
    /// Request permission from the user for a specific operation
    async fn request_permission(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<PermissionState>;

    /// Request permission with timeout
    async fn request_permission_timeout(
        &self,
        request: &PermissionRequest,
        timeout: Duration,
    ) -> PermissionResult<PermissionState>;

    /// Format permission request for display
    fn format_request(&self, request: &PermissionRequest) -> String;
}

/// Default timeout for permission requests (30 seconds)
pub const DEFAULT_REQUEST_TIMEOUT: Duration = Duration::from_secs(30);