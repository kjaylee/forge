mod types;

pub use types::{Command, Permission, Policy, Whitelisted};
pub use types::Config as PermissionConfig;

/// Error type for permission operations
#[derive(Debug, thiserror::Error)]
pub enum PermissionError {
    #[error("Operation not permitted: {0}")]
    OperationNotPermitted(String),
}

/// Result type for permission operations
pub type PermissionResult<T> = std::result::Result<T, PermissionError>;