use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Basic permission types that tools can request
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Permission {
    Read,
    Write,
    Execute,
}

/// Policy for permission decisions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Policy<T> {
    Once,
    Always(Whitelisted<T>),
}

/// Whitelist configuration for allowed operations
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Whitelisted<T> {
    Some(Vec<T>),
    All,
}

/// Command type for executable permissions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Command(pub String);

/// Global permission configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    /// Permission policies by type
    pub policies: HashMap<Permission, Policy<Command>>,
}

impl Default for Config {
    fn default() -> Self {
        let mut policies = HashMap::new();
        policies.insert(Permission::Read, Policy::Once);
        policies.insert(Permission::Write, Policy::Once);
        policies.insert(Permission::Execute, Policy::Once);
        Self { policies }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = Config::default();
        assert!(matches!(config.policies.get(&Permission::Read), Some(Policy::Once)));
        assert!(matches!(config.policies.get(&Permission::Write), Some(Policy::Once)));
        assert!(matches!(config.policies.get(&Permission::Execute), Some(Policy::Once)));
    }

    #[test]
    fn test_allowed_commands() {
        let mut config = Config::default();
        let whitelist = Whitelisted::Some(vec![
            Command("ls".to_string()),
            Command("git".to_string()),
        ]);
        config.policies.insert(Permission::Execute, Policy::Always(whitelist));
        
        match config.policies.get(&Permission::Execute) {
            Some(Policy::Always(Whitelisted::Some(commands))) => {
                assert_eq!(commands.len(), 2);
                assert_eq!(commands[0].0, "ls");
                assert_eq!(commands[1].0, "git");
            }
            _ => panic!("Expected Always policy with Some whitelist"),
        }
    }

    #[test]
    fn test_allow_all_reads() {
        let mut config = Config::default();
        config.policies.insert(Permission::Read, Policy::Always(Whitelisted::All));
        
        match config.policies.get(&Permission::Read) {
            Some(Policy::Always(Whitelisted::All)) => (),
            _ => panic!("Expected Always policy with All whitelist"),
        }
    }
}