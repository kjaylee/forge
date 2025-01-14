use std::collections::HashMap;

use serde::{Deserialize, Deserializer, Serialize};
use serde_yaml::Value;

/// Basic permission types that tools can request
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Permission {
    Read,
    Write,
    Execute,
}

/// Policy for permission decisions.
///
/// `#[serde(untagged)]` means:
/// - a simple string `"once"` → `Policy::Once`,
/// - a map with key `"Always"` → `Policy::Always(...)`.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(untagged)]
pub enum Policy {
    Once,
    Always(Whitelisted<Command>),
}

impl<'de> Deserialize<'de> for Policy {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let val = Value::deserialize(deserializer)?;

        match &val {
            // Simple "once" string
            Value::String(s) if s.to_lowercase() == "once" => Ok(Policy::Once),

            // Simple "always", "all" string, or "Always: all" string
            Value::String(s) => {
                let lower = s.to_lowercase();
                if lower.contains("always") || lower.contains("all") {
                    let whitelisted =
                        Whitelisted::<Command>::deserialize(Value::String("All".to_string()))
                            .map_err(serde::de::Error::custom)?;
                    Ok(Policy::Always(whitelisted))
                } else {
                    Err(serde::de::Error::custom(
                        "Expected 'once', 'always', or 'all' configuration",
                    ))
                }
            }

            // Mapping with various Always/All configurations
            Value::Mapping(map) => {
                // Support various key variations
                let always_keys = ["Always", "always", "All", "all"];

                for key in always_keys.iter() {
                    if let Some(inner_val) = map.get(Value::String(key.to_string())) {
                        let whitelisted = match inner_val {
                            // Simple "All"
                            Value::String(s) if s.to_lowercase() == "all" => {
                                Whitelisted::<Command>::All
                            }
                            // Nested mapping
                            Value::Mapping(_) => {
                                Whitelisted::<Command>::deserialize(inner_val.clone())
                                    .map_err(serde::de::Error::custom)?
                            }
                            // Default to All for other cases
                            _ => Whitelisted::<Command>::All,
                        };
                        return Ok(Policy::Always(whitelisted));
                    }
                }

                Err(serde::de::Error::custom(
                    "Expected 'Always' or 'All' configuration",
                ))
            }

            // Fallback: sequences or other types
            _ => {
                let whitelisted = Whitelisted::<Command>::deserialize(val.clone())
                    .map_err(serde::de::Error::custom)?;
                Ok(Policy::Always(whitelisted))
            }
        }
    }
}

impl Policy {
    pub fn normalize(self) -> Self {
        // Left here in case you want to transform variants in the future.
        self
    }
}
pub struct PermissionRequest {
    pub permissions: Vec<Permission>,
    pub cmd: Option<String>,
}

impl PermissionRequest {
    pub fn new(permissions: Vec<Permission>, cmd: Option<String>) -> Self {
        Self { permissions, cmd }
    }
}
/// Whitelist configuration for allowed operations:
/// - `"All"` means "allow everything".
/// - `"Some": [...]` means "allow only these specific commands, paths, etc."
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Whitelisted<T> {
    All,
    Some(Vec<T>),
}

// -- CUSTOM DESERIALIZE IMPL --
//
// We manually implement Deserialize so that a YAML string "All" becomes
// `Whitelisted::All`, and a YAML map with `Some: [...]` becomes
// `Whitelisted::Some(Vec<T>)`.
//
// Example valid YAML shapes:
//   "All"
//   Some:
//     - "ls"
//     - "git status"
//
impl<'de, T> Deserialize<'de> for Whitelisted<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Whitelisted<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        // We'll first parse it into `serde_yaml::Value` to see its shape.
        let val = Value::deserialize(deserializer)?;

        match val.clone() {
            // If it's a string "All"
            Value::String(s) if s.to_lowercase() == "all" => Ok(Whitelisted::All),

            // If it's a mapping with "All" or "Something"
            Value::Mapping(ref map) => {
                // If there's a direct match with "All"
                if map.get(Value::String("All".to_string())).is_some() {
                    return Ok(Whitelisted::All);
                }

                // If there's a "Some" key
                if let Some(some_val) = map.get(Value::String("Some".to_string())) {
                    let items = Vec::<T>::deserialize(some_val.clone())
                        .map_err(serde::de::Error::custom)?;
                    return Ok(Whitelisted::Some(items));
                }

                // Special handling for nested Always
                if let Some(inner_val) = map.get(Value::String("Always".to_string())) {
                    match inner_val {
                        Value::String(s) if s.to_lowercase() == "all" => {
                            return Ok(Whitelisted::All);
                        }
                        Value::Mapping(inner_map) => {
                            if let Some(some_val) =
                                inner_map.get(Value::String("Some".to_string()))
                            {
                                let items = Vec::<T>::deserialize(some_val.clone())
                                    .map_err(serde::de::Error::custom)?;
                                return Ok(Whitelisted::Some(items));
                            }
                        }
                        _ => {}
                    }
                }

                Err(serde::de::Error::custom(
                    "Expected 'All', 'Some', or nested 'Always' configuration",
                ))
            }

            // If it's a sequence (bare list)
            Value::Sequence(seq) => {
                let items = Vec::<T>::deserialize(Value::Sequence(seq.clone()))
                    .map_err(serde::de::Error::custom)?;
                Ok(Whitelisted::Some(items))
            }

            // If it's anything else
            _ => Err(serde::de::Error::custom(
                "Unsupported configuration for Whitelisted type",
            )),
        }
    }
}

/// Command type for executable permissions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Command(pub String);

/// Global permission configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionConfig {
    /// Permission policies by type
    pub policies: HashMap<Permission, Policy>,
}

impl Default for PermissionConfig {
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
        let config = PermissionConfig::default();
        assert!(matches!(
            config.policies.get(&Permission::Read),
            Some(Policy::Once)
        ));
        assert!(matches!(
            config.policies.get(&Permission::Write),
            Some(Policy::Once)
        ));
        assert!(matches!(
            config.policies.get(&Permission::Execute),
            Some(Policy::Once)
        ));
    }

    #[test]
    fn test_allowed_commands() {
        let mut config = PermissionConfig::default();
        let whitelist =
            Whitelisted::Some(vec![Command("ls".to_string()), Command("git".to_string())]);
        config
            .policies
            .insert(Permission::Execute, Policy::Always(whitelist));

        match config.policies.get(&Permission::Execute) {
            Some(Policy::Always(Whitelisted::Some(commands))) => {
                assert_eq!(commands.len(), 2);
                assert_eq!(commands[0].0, "ls");
                assert_eq!(commands[1].0, "git");
            }
            _ => panic!("Expected Always(Whitelisted::Some([...])) for Execute"),
        }
    }

    #[test]
    fn test_allow_all_reads() {
        let mut config = PermissionConfig::default();
        config
            .policies
            .insert(Permission::Read, Policy::Always(Whitelisted::All));

        match config.policies.get(&Permission::Read) {
            Some(Policy::Always(Whitelisted::All)) => (),
            _ => panic!("Expected read policy to be Always(All)"),
        }
    }
}
