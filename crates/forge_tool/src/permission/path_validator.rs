//! Path validation using forge_walker.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use forge_domain::PermissionResult;
use forge_walker::Walker;
use tokio::sync::RwLock;

/// Validates and normalizes paths for permission checks.
pub struct PathValidator {
    cwd: PathBuf,
    walker: Arc<RwLock<Option<Walker>>>,
}

impl Clone for PathValidator {
    fn clone(&self) -> Self {
        Self { cwd: self.cwd.clone(), walker: Arc::new(RwLock::new(None)) }
    }
}

impl PathValidator {
    /// Creates a new path validator for the given working directory.
    pub fn new(cwd: PathBuf) -> Self {
        Self { cwd, walker: Arc::new(RwLock::new(None)) }
    }

    /// Get the current working directory
    pub fn cwd(&self) -> PathBuf {
        self.cwd.clone()
    }

    /// Validates if a path is accessible and returns its normalized form.
    pub async fn validate_path(
        &self,
        path: &Path,
        max_depth: Option<usize>,
    ) -> PermissionResult<PathBuf> {
        tracing::debug!("Validating path: {}", path.display());
        // For existing paths, use canonicalize
        let path = if path.exists() {
            path.canonicalize().map_err(|_| {
                forge_domain::PermissionError::InvalidPath(path.to_string_lossy().to_string())
            })?
        } else {
            // For non-existent paths, use absolute path
            if path.is_absolute() {
                path.to_path_buf()
            } else {
                self.cwd.join(path)
            }
        };

        // Paths outside CWD are allowed but will require permission

        let mut walker_guard = self.walker.write().await;
        if walker_guard.is_none() {
            *walker_guard = Some(Walker::new(self.cwd.clone()));
        }

        // Clone the walker for this operation
        let walker = Walker::new(self.cwd.clone());

        // Add max_depth if specified
        let walker = if let Some(depth) = max_depth {
            walker.with_max_depth(depth)
        } else {
            walker
        };

        // For paths within CWD, verify they exist in the walker's output
        if path.exists() && path.starts_with(&self.cwd) {
            let files = walker.get()
                .await
                .map_err(forge_domain::PermissionError::WalkerError)?;

            let relative_path = path.strip_prefix(&self.cwd).map_err(|_| {
                forge_domain::PermissionError::InvalidPath(path.to_string_lossy().to_string())
            })?;
            let path_str = relative_path.to_string_lossy().to_string();

            if !files.iter().any(|f| f.path == path_str) {
                return Err(forge_domain::PermissionError::InvalidPath(path_str));
            }
        } else if !path.exists() {
            // For new files, just check if parent exists
            let parent = path.parent().ok_or_else(|| {
                forge_domain::PermissionError::InvalidPath("No parent directory".to_string())
            })?;
            if !parent.exists() {
                std::fs::create_dir_all(parent).map_err(|e| {
                    forge_domain::PermissionError::InvalidPath(format!(
                        "Failed to create parent directory {}: {}",
                        parent.display(),
                        e
                    ))
                })?;
            }
        }

        Ok(path)
    }
}

#[cfg(test)]
mod tests {
    use std::env;

    use super::*;

    impl PathValidator {
        fn is_within_cwd(&self, path: &Path) -> bool {
            path.starts_with(&self.cwd)
        }
    }

    #[tokio::test]
    async fn test_path_validation() {
        let cwd = env::current_dir().unwrap();
        let validator = PathValidator::new(cwd.clone());

        // Test valid path
        let path = cwd.join("Cargo.toml");
        let result = validator.validate_path(&path, None).await;
        assert!(result.is_ok());

        // Test invalid path
        let path = PathBuf::from("/invalid/path");
        let result = validator.validate_path(&path, None).await;
        assert!(result.is_err());

        // Test path outside CWD is now allowed
        let path = cwd.join("..").canonicalize().unwrap();
        let result = validator.validate_path(&path, None).await;
        assert!(result.is_ok());
    }

    #[test]
    fn test_is_within_cwd() {
        let cwd = env::current_dir().unwrap();
        let validator = PathValidator::new(cwd.clone());

        // Test path within CWD
        let path = cwd.join("some/path");
        assert!(validator.is_within_cwd(&path));

        // Test path outside CWD
        let path = PathBuf::from("/some/other/path");
        assert!(!validator.is_within_cwd(&path));
    }
}
