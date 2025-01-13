mod types;
mod loader;

// Re-export all public items
pub use loader::{load_config, LoadError, load_or_default};
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

    #[error("Walker error: {0}")]
    WalkerError(#[from] forge_walker::Error),
}

/// Result type for permission operations
pub type PermissionResult<T> = std::result::Result<T, PermissionError>;