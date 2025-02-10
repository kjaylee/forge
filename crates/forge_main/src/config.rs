#![allow(dead_code)]
use std::collections::HashMap;

use strum_macros::{Display, EnumString};

use crate::info::Info;

/// decent defaults for the config.
const PRIMARY_MODEL: &str = "anthropic/claude-3.5-sonnet";
const SECONDARY_MODEL: &str = "anthropic/claude-3.5-haiku";
const TOOL_TIMEOUT: u64 = 300;

#[derive(Debug, Clone, PartialEq, Eq, Hash, EnumString, Display)]
pub enum ConfigKey {
    #[strum(serialize = "primary-model")]
    PrimaryModel,
    #[strum(serialize = "secondary-model")]
    SecondaryModel,
    #[strum(serialize = "tool-timeout")]
    ToolTimeout,
}

impl ConfigKey {
    pub fn as_str(&self) -> &'static str {
        match self {
            ConfigKey::PrimaryModel => "primary-model",
            ConfigKey::SecondaryModel => "secondary-model",
            ConfigKey::ToolTimeout => "tool-timeout",
        }
    }
}

/// Represents configuration values with their specific types
#[derive(Debug, Clone)]
pub enum ConfigValue {
    /// Model identifier string
    Model(String),
    /// Tool timeout in seconds
    ToolTimeout(u64),
}

/// Main configuration structure holding all config values
#[derive(Debug)]
pub struct Config(HashMap<ConfigKey, ConfigValue>);

impl Config {
    pub fn load() -> Self {
        // load the config from the .forgerc file
        dotenv::from_filename(".forgerc").ok();

        // load the config from environment variables if not set use defaults.
        let primary_model = std::env::var("FORGE_LARGE_MODEL").unwrap_or(PRIMARY_MODEL.to_string());
        let secondary_model =
            std::env::var("FORGE_SMALL_MODEL").unwrap_or(SECONDARY_MODEL.to_string());
        let tool_timeout = std::env::var("TOOL_TIMEOUT").unwrap_or(TOOL_TIMEOUT.to_string());

        // create a new config map
        let mut values = HashMap::new();
        values.insert(ConfigKey::PrimaryModel, ConfigValue::Model(primary_model));
        values.insert(
            ConfigKey::SecondaryModel,
            ConfigValue::Model(secondary_model),
        );
        values.insert(
            ConfigKey::ToolTimeout,
            ConfigValue::ToolTimeout(tool_timeout.parse().expect("failed to parse tool timeout")),
        );
        Self(values)
    }
}

impl ConfigValue {
    /// Returns the string representation of the configuration value
    pub fn as_str(&self) -> String {
        match self {
            ConfigValue::Model(model) => model.clone(),
            ConfigValue::ToolTimeout(timeout) => timeout.to_string(),
        }
    }
}

impl std::fmt::Display for ConfigValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Config {
    /// Returns the primary model configuration
    pub fn primary_model(&self) -> String {
        self.get_model(&ConfigKey::PrimaryModel)
            .unwrap_or(PRIMARY_MODEL.to_string())
    }

    /// Returns the secondary model configuration
    pub fn secondary_model(&self) -> String {
        self.get_model(&ConfigKey::SecondaryModel)
            .unwrap_or(SECONDARY_MODEL.to_string())
    }

    /// Returns the tool timeout configuration
    pub fn tool_timeout(&self) -> u64 {
        self.get(&ConfigKey::ToolTimeout)
            .and_then(|v| match v {
                ConfigValue::ToolTimeout(t) => Some(*t),
                _ => None,
            })
            .unwrap_or(TOOL_TIMEOUT)
    }

    /// Helper method to get model configuration
    fn get_model(&self, key: &ConfigKey) -> Option<String> {
        self.0.get(key).and_then(|v| match v {
            ConfigValue::Model(m) => Some(m.clone()),
            _ => None,
        })
    }

    /// Gets a configuration value by key string
    fn get(&self, key: &ConfigKey) -> Option<&ConfigValue> {
        self.0.get(key)
    }
}

impl From<&Config> for Info {
    fn from(config: &Config) -> Self {
        let mut info = Info::new().add_title("Configuration");
        if config.0.is_empty() {
            info = info.add_item("Status", "No configurations set");
        } else {
            let mut configs: Vec<_> = config.0.iter().collect();
            configs.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str())); // Sort by key string
            for (key, value) in configs {
                info = info.add_item(key.as_str(), value.as_str());
            }
        }
        info
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load() {
        let config = Config::load();
        assert_eq!(config.0.len(), 3);
        // check that all values are set
        assert!(!config.primary_model().is_empty());
        assert!(!config.secondary_model().is_empty());
        assert!(config.tool_timeout() > 0);
    }
}
