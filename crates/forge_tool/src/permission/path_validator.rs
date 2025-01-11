//! Path validation using forge_walker.

use std::path::{Path, PathBuf};
use std::sync::Arc;
use tokio::sync::RwLock;

use forge_domain::PermissionResult;
use forge_walker::Walker;

/// Validates and normalizes paths for permission checks.
pub struct PathValidator {
    cwd: PathBuf,
    walker: Arc<RwLock<Option<Walker>>>,
}

impl Clone for PathValidator {
    fn clone(&self) -> Self {
        Self {
            cwd: self.cwd.clone(),
            walker: Arc::new(RwLock::new(None)),
        }
    }
}

impl PathValidator {
    /// Creates a new path validator for the given working directory.
    pub fn new(cwd: PathBuf) -> Self {
        Self {
            cwd,
            walker: Arc::new(RwLock::new(None)),
        }
    }

    /// Returns the working directory this validator is configured for.
    pub fn cwd(&self) -> &Path {
        &self.cwd
    }

    /// Validates if a path is accessible and returns its normalized form.
    pub async fn validate_path(&self, path: &Path, max_depth: Option<usize>) -> PermissionResult<PathBuf> {
        // First, try to canonicalize the path
        let path = path.canonicalize()
            .map_err(|_| forge_domain::PermissionError::InvalidPath(path.to_string_lossy().to_string()))?;

        // Check if the path is within CWD
        if !path.starts_with(&self.cwd) {
            return Err(forge_domain::PermissionError::OutsideAllowedDirectory(path));
        }

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

        // Use walker to validate the path exists and is accessible
        let files = walker.get().await
            .map_err(|e| forge_domain::PermissionError::WalkerError(e))?;

        // Check if the path exists in walker's output
        let relative_path = path.strip_prefix(&self.cwd)
            .map_err(|_| forge_domain::PermissionError::InvalidPath(path.to_string_lossy().to_string()))?;
        let path_str = relative_path.to_string_lossy().to_string();

        if files.iter().any(|f| f.path == path_str) {
            Ok(path)
        } else {
            Err(forge_domain::PermissionError::InvalidPath(path_str))
        }
    }

    /// Checks if a path is within the allowed directory structure.
    pub fn is_within_cwd(&self, path: &Path) -> bool {
        path.starts_with(&self.cwd)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

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

        // Test path outside CWD
        let path = cwd.join("..").canonicalize().unwrap();
        let result = validator.validate_path(&path, None).await;
        assert!(result.is_err());
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