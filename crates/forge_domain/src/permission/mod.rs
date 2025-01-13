mod loader;
mod types;

// Re-export all public items
pub use loader::{load_config, load_or_default, LoadError};
pub use types::{Permission, PermissionConfig, Policy};

/// Error type for permission operations
#[derive(Debug, thiserror::Error)]
pub enum PermissionError {
    #[error("Path not found or inaccessible: {0}")]
    InvalidPath(String),

    #[error("Path outside allowed directory: {0}")]
    OutsideAllowedDirectory(std::path::PathBuf),

    #[error("Operation not permitted: {0}")]
    OperationNotPermitted(String),
}

/// Result type for permission operations
pub type PermissionResult<T> = std::result::Result<T, PermissionError>;
