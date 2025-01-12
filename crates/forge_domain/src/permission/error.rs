//! Error types for the permission system.

use std::path::PathBuf;
use thiserror::Error;

/// Errors that can occur in the permission system.
#[derive(Debug, Error)]
pub enum PermissionError {
    /// Access denied by user
    #[error("User denied access to {0}")]
    UserDenied(PathBuf),

    /// Access denied by system
    #[error("System denied access to {0}")]
    SystemDenied(PathBuf),

    /// Invalid response from user interaction
    #[error("Invalid permission response")]
    InvalidResponse,

    /// Interaction with user failed
    #[error("Permission interaction failed: {0}")]
    InteractionFailed(String),

    /// Timeout during interaction
    #[error("Permission request timed out")]
    InteractionTimeout,

    /// The path is outside the allowed directory
    #[error("Path {0} is outside allowed directory")]
    OutsideAllowedDirectory(PathBuf),

    /// Session has expired
    #[error("Permission session has expired")]
    SessionExpired,

    /// Configuration error
    #[error("Permission config error: {0}")]
    ConfigError(String),

    /// Storage error
    #[error("Permission storage error: {0}")]
    StorageError(String),

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// Error from file system walker
    #[error("File system error: {0}")]
    WalkerError(#[from] forge_walker::Error),
}

/// Result type for permission operations
pub type PermissionResult<T> = std::result::Result<T, PermissionError>;
