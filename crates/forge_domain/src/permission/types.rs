use std::path::PathBuf;
use serde::{Deserialize, Serialize};

use super::PermissionState;

/// Represents a permission for a specific path and tool
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Permission {
    /// The state of the permission
    pub state: PermissionState,
    /// The path this permission applies to
    path: PathBuf,
    /// The tool this permission applies to
    tool_name: String,
}

impl Permission {
    /// Create a new permission
    pub fn new(
        state: PermissionState,
        path: impl Into<PathBuf>,
        tool_name: impl Into<String>,
    ) -> Self {
        Self {
            state,
            path: path.into(),
            tool_name: tool_name.into(),
        }
    }

    /// Get the state of this permission
    pub fn state(&self) -> &PermissionState {
        &self.state
    }

    /// Get the path this permission applies to
    pub fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Get the tool name this permission applies to
    pub fn tool_name(&self) -> &str {
        &self.tool_name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permission_creation() {
        let perm = Permission::new(
            PermissionState::Allow,
            "/test/path",
            "test_tool",
        );

        assert!(matches!(perm.state(), PermissionState::Allow));
        assert_eq!(perm.path().to_str().unwrap(), "/test/path");
        assert_eq!(perm.tool_name(), "test_tool");
    }

    #[test]
    fn test_permission_cloning() {
        let original = Permission::new(
            PermissionState::AllowForever,
            "/test/path",
            "test_tool",
        );

        let cloned = original.clone();

        assert!(matches!(cloned.state(), PermissionState::AllowForever));
        assert_eq!(cloned.path(), original.path());
        assert_eq!(cloned.tool_name(), original.tool_name());
    }
}