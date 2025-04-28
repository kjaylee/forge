//! # ForgeFS
//!
//! A file system abstraction layer that standardizes error handling for file
//! operations.
//!
//! ForgeFS wraps tokio's filesystem operations with consistent error context
//! using anyhow::Context. Each method provides standardized error messages in
//! the format "Failed to [operation] [path]", ensuring uniform error reporting
//! throughout the application while preserving the original error cause.

mod binary_detection;
mod error;
mod file_info;
mod file_size;
mod meta;
mod read;
mod read_range;
mod utf8_boundary;
mod write;

pub use crate::error::ForgeFileError;
pub use crate::file_info::FileInfo;

/// ForgeFS provides a standardized interface for file system operations
/// with consistent error handling.
#[derive(Debug)]
pub struct ForgeFS;
