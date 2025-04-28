use std::string::FromUtf8Error;

use thiserror::Error;

/// Error type for file operations
#[derive(Error, Debug)]
pub enum ForgeFileError {
    #[error("Binary files are not supported. File detected as {0}")]
    BinaryFileNotSupported(String),

    #[error("Invalid range: {0}")]
    InvalidRange(String),

    #[error("UTF-8 validation failed: {0}")]
    Utf8ValidationFailed(#[from] FromUtf8Error),

    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
}
