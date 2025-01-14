mod types;

pub use types::*;

/// Error type for permission operations
#[derive(Debug, thiserror::Error)]
pub enum PermissionError {
    #[error("Operation not permitted: {0}")]
    OperationNotPermitted(String),
}

/// Result type for permission operations
pub type PermissionResult<T> = std::result::Result<T, PermissionError>;
