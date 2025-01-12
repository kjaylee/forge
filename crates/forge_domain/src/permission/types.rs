use std::collections::HashMap;
use std::path::PathBuf;
use serde::{Deserialize, Serialize};

/// Basic permission types for file system operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Permission {
    /// Read file contents
    Read,
    /// Write or modify files
    Write,
    /// Execute commands or scripts
    Execute,
    /// No access allowed
    Deny,
}

/// Permission policy for decisions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Policy {
    /// Always allow without asking
    Always,
    /// Allow only once
    Once,  
    /// Allow for the current session
    Session,
}

/// Global permission configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionConfig {
    /// Default policy for unspecified permissions
    pub default_policy: Policy,
    /// Specific policies for different permission types
    pub permissions: HashMap<Permission, Policy>,
    /// Glob patterns for paths that are always denied
    pub deny_patterns: Vec<String>,
}

impl Default for PermissionConfig {
    fn default() -> Self {
        Self {
            default_policy: Policy::Session,
            permissions: HashMap::new(),
            deny_patterns: vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = PermissionConfig::default();
        assert_eq!(config.default_policy, Policy::Session);
        assert!(config.permissions.is_empty());
        assert!(config.deny_patterns.is_empty());
    }

    #[test]
    fn test_permission_config() {
        let mut config = PermissionConfig::default();
        config.permissions.insert(Permission::Read, Policy::Always);
        config.permissions.insert(Permission::Write, Policy::Session);
        config.deny_patterns.push("**/secrets/**".to_string());

        assert_eq!(config.permissions.get(&Permission::Read), Some(&Policy::Always));
        assert_eq!(config.permissions.get(&Permission::Write), Some(&Policy::Session));
        assert_eq!(config.deny_patterns.len(), 1);
    }
}
