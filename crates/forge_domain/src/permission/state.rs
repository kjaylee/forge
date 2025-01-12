use serde::{Deserialize, Serialize};

/// Represents the state of a permission decision
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum PermissionState {
    /// Denied for this request only
    Reject,
    /// Allowed for this request only
    Allow,
    /// Allowed for the duration of the session
    AllowSession,
    /// Allowed and saved to configuration
    AllowForever,
}

impl PermissionState {
    /// Returns true if this represents any kind of allow state
    pub fn is_allowed(&self) -> bool {
        matches!(self, 
            Self::Allow | 
            Self::AllowSession | 
            Self::AllowForever
        )
    }

    /// Returns true if this permission should be saved to config
    pub fn save_to_config(&self) -> bool {
        matches!(self, Self::AllowForever)
    }

    /// Returns true if this permission should be kept in session
    pub fn save_to_session(&self) -> bool {
        matches!(self, Self::AllowSession)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permission_states_allow_checks() {
        assert!(PermissionState::Allow.is_allowed());
        assert!(PermissionState::AllowSession.is_allowed());
        assert!(PermissionState::AllowForever.is_allowed());
        assert!(!PermissionState::Reject.is_allowed());
    }

    #[test]
    fn test_permission_states_storage() {
        assert!(PermissionState::AllowForever.save_to_config());
        assert!(!PermissionState::Allow.save_to_config());
        assert!(!PermissionState::AllowSession.save_to_config());
        assert!(!PermissionState::Reject.save_to_config());

        assert!(PermissionState::AllowSession.save_to_session());
        assert!(!PermissionState::Allow.save_to_session());
        assert!(!PermissionState::AllowForever.save_to_session());
        assert!(!PermissionState::Reject.save_to_session());
    }

    #[test]
    fn test_permission_states_serialization() {
        let state = PermissionState::AllowForever;
        let serialized = serde_json::to_string(&state).unwrap();
        let deserialized: PermissionState = serde_json::from_str(&serialized).unwrap();
        assert_eq!(state, deserialized);
    }
}