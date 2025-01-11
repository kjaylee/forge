//! Core types for the permission system.

use std::path::PathBuf;

use super::PermissionState;

/// Represents a permission for a specific tool and path.
#[derive(Debug, Clone)]
pub struct Permission {
    /// The state of the permission (deny, allow once, etc.)
    pub state: PermissionState,
    /// The path this permission applies to
    pub path: PathBuf,
    /// The tool this permission applies to
    pub tool_name: String,
    /// Indicates if this permission is still active in the current session
    pub active: bool,
}

impl Permission {
    /// Creates a new permission
    pub fn new(
        state: PermissionState,
        path: PathBuf,
        tool_name: String,
    ) -> Self {
        Self {
            state,
            path,
            tool_name,
            active: true,
        }
    }

    /// Deactivates this permission
    pub fn deactivate(&mut self) {
        self.active = false;
    }

    /// Returns whether this permission is currently valid
    pub fn is_valid(&self) -> bool {
        self.active && match self.state {
            PermissionState::Deny => false,
            PermissionState::AllowOnce => true,  // Will be deactivated after use
            PermissionState::AllowSession => true,
            PermissionState::AllowDirectory => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permission_validity() {
        let path = PathBuf::from("/test/path");
        
        // Test AllowSession permission
        let perm = Permission::new(
            PermissionState::AllowSession,
            path.clone(),
            "fs_read".to_string(),
        );
        assert!(perm.is_valid());
        
        // Test Deny permission
        let perm = Permission::new(
            PermissionState::Deny,
            path.clone(),
            "fs_read".to_string(),
        );
        assert!(!perm.is_valid());

        // Test deactivation
        let mut perm = Permission::new(
            PermissionState::AllowSession,
            path,
            "fs_read".to_string(),
        );
        assert!(perm.is_valid());
        perm.deactivate();
        assert!(!perm.is_valid());
    }
}