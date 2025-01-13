use std::path::Path;

use forge_domain::{PermissionError, PermissionResult};

/// Result display helper
#[derive(Debug)]
pub struct PermissionResultDisplay {
    allowed: bool,    
    message: String,
}

impl PermissionResultDisplay {
    /// Create simple display for permission result
    pub fn new(allowed: bool, path: &Path) -> Self {
        let message = format!(
            "Permission {} for {}",
            if allowed { "granted" } else { "denied" },
            path.display()
        );
        Self { allowed, message }
    }

    /// Create rich display with error message and permission details
    pub fn with_error(allowed: bool, path: &Path, error: Option<String>) -> Self {
        let mut message = format!(
            "Permission {} for {}",
            if allowed { "granted" } else { "denied" },
            path.display()
        );

        if let Some(err) = error {
            message = format!("{}: {}", message, err);
        }

        Self { allowed, message }
    }
}

impl std::fmt::Display for PermissionResultDisplay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

pub trait AsPermissionDisplay {
    fn as_display(&self) -> PermissionResultDisplay;
}

impl<T> AsPermissionDisplay for PermissionResult<T> {
    fn as_display(&self) -> PermissionResultDisplay {
        match self {
            Ok(_) => PermissionResultDisplay::new(true, Path::new("/")),
            Err(PermissionError::OperationNotPermitted(msg)) => {
                PermissionResultDisplay::new(false, Path::new(msg))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_display_simple() {
        let path = PathBuf::from("/test/path");
        let result = PermissionResultDisplay::new(true, &path);
        assert_eq!(result.to_string(), "Permission granted for /test/path");

        let result = PermissionResultDisplay::new(false, &path);
        assert_eq!(result.to_string(), "Permission denied for /test/path");
    }

    #[test]
    fn test_as_display() {
        let result: PermissionResult<()> = Ok(());
        let display = result.as_display();
        assert!(display.allowed);
        assert_eq!(display.to_string(), "Permission granted for /");

        let result: PermissionResult<()> =
            Err(PermissionError::OperationNotPermitted("test error".to_string()));
        let display = result.as_display();
        assert!(!display.allowed);
        assert_eq!(display.to_string(), "Permission denied for test error");
    }
}