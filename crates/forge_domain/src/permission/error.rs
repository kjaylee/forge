//! Error types for the permission system.

use std::path::PathBuf;
use thiserror::Error;

/// Errors that can occur in the permission system.
#[derive(Debug, Error)]
pub enum PermissionError {
    /// Access to the requested path is denied
    #[error("Access denied to path: {0}")]
    AccessDenied(PathBuf),

    /// The path is outside the allowed directory
    #[error("Path {0} is outside the allowed directory")]
    OutsideAllowedDirectory(PathBuf),

    /// Session has expired
    #[error("Permission session has expired")]
    SessionExpired,

    /// Walker related error
    #[error("File system walker error: {0}")]
    WalkerError(#[from] forge_walker::Error),

    /// Invalid path
    #[error("Invalid path: {0}")]
    InvalidPath(String),

    /// Configuration file error
    #[error("Configuration error: {0}")]
    ConfigError(String),

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// YAML parsing error
    #[error("YAML parsing error: {0}")]
    YamlError(#[from] serde_yaml::Error),

    /// Home directory not found
    #[error("Could not determine home directory")]
    HomeDirectoryNotFound,

    /// Environment variable error
    #[error("Environment variable error: {0}")]
    EnvVarError(#[from] std::env::VarError),
}

/// Result type for permission operations
pub type PermissionResult<T> = std::result::Result<T, PermissionError>;