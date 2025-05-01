use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// Output from a command execution with regular-sized output
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommandOutput {
    /// Standard output from the command
    pub stdout: String,
    /// Standard error from the command
    pub stderr: String,
    /// Whether the command succeeded (exit code 0)
    pub success: bool,
}

/// Output from a command execution with truncated content for very large
/// outputs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TruncatedCommandOutput {
    /// Standard output from the command, truncated
    pub stdout: String,
    /// Standard error from the command, truncated
    pub stderr: String,
    /// Whether the command succeeded (exit code 0)
    pub success: bool,
    /// Original stdout length before truncation
    pub original_stdout_length: usize,
    /// Original stderr length before truncation
    pub original_stderr_length: usize,
    /// Path to the temporary file containing the full output, if available
    pub temp_file_path: Option<PathBuf>,
}

impl CommandOutput {
    /// Creates a new command output
    pub fn new(stdout: String, stderr: String, success: bool) -> Self {
        Self { stdout, stderr, success }
    }

    /// Converts this command output into a truncated version
    pub fn into_truncated(
        self,
        truncated_stdout: String,
        truncated_stderr: String,
        original_stdout_length: usize,
        original_stderr_length: usize,
        temp_file_path: Option<PathBuf>,
    ) -> TruncatedCommandOutput {
        TruncatedCommandOutput {
            stdout: truncated_stdout,
            stderr: truncated_stderr,
            success: self.success,
            original_stdout_length,
            original_stderr_length,
            temp_file_path,
        }
    }
}

impl TruncatedCommandOutput {
    /// Creates a new truncated command output
    pub fn new(
        stdout: String,
        stderr: String,
        success: bool,
        original_stdout_length: usize,
        original_stderr_length: usize,
        temp_file_path: Option<PathBuf>,
    ) -> Self {
        Self {
            stdout,
            stderr,
            success,
            original_stdout_length,
            original_stderr_length,
            temp_file_path,
        }
    }

    /// Returns the original size of stdout before truncation
    pub fn stdout_size(&self) -> usize {
        self.original_stdout_length
    }

    /// Returns the original size of stderr before truncation
    pub fn stderr_size(&self) -> usize {
        self.original_stderr_length
    }

    /// Returns true if a temporary file exists with the full output
    pub fn has_temp_file(&self) -> bool {
        self.temp_file_path.is_some()
    }

    /// Returns the path to the temporary file, if one exists
    pub fn temp_file_path(&self) -> Option<&PathBuf> {
        self.temp_file_path.as_ref()
    }
}
