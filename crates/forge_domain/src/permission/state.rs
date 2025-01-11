//! Permission state handling for the forge system.

use serde::{Deserialize, Serialize};

/// Represents the different states a permission can be in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PermissionState {
    /// Permission is explicitly denied
    Deny,
    /// Permission is granted for a single operation
    AllowOnce,
    /// Permission is granted for the current session
    AllowSession,
    /// Permission is granted for a specific directory and its subdirectories
    AllowDirectory,
}

impl Default for PermissionState {
    fn default() -> Self {
        Self::Deny
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permission_state_default() {
        assert_eq!(PermissionState::default(), PermissionState::Deny);
    }

    #[test]
    fn test_permission_state_serialization() {
        let state = PermissionState::AllowSession;
        let serialized = serde_json::to_string(&state).unwrap();
        let deserialized: PermissionState = serde_json::from_str(&serialized).unwrap();
        assert_eq!(state, deserialized);
    }
}