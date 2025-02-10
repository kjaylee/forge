#![allow(dead_code)]
use std::collections::HashMap;

#[derive(Debug, Eq, PartialEq, Hash)]
enum ConfigKey {
    PrimaryModel,
    SecondaryModel,
    ToolTimeout,
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
        dotenv::from_filename(".forgerc").expect("failed to load `.forgerc` file");

        // load the config from environment variables if not set use defaults.
        let primary_model =
            std::env::var("FORGE_LARGE_MODEL").unwrap_or("anthropic/claude-3.5-sonnet".to_string());
        let secondary_model =
            std::env::var("FORGE_SMALL_MODEL").unwrap_or("anthropic/claude-3.5-haiku".to_string());
        let tool_timeout = std::env::var("TOOL_TIMEOUT").unwrap_or("300".to_string());

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
    /// Returns the primary model configuration if set
    pub fn primary_model(&self) -> String {
        self.get_model(&ConfigKey::PrimaryModel)
            .unwrap_or("anthropic/claude-3.5-sonnet".to_string())
    }

    /// Returns the secondary model configuration if set
    pub fn secondary_model(&self) -> String {
        self.get_model(&ConfigKey::SecondaryModel)
            .unwrap_or("anthropic/claude-3.5-haiku".to_string())
    }

    /// Returns the tool timeout configuration if set
    pub fn tool_timeout(&self) -> u64 {
        self.get(&ConfigKey::ToolTimeout)
            .and_then(|v| match v {
                ConfigValue::ToolTimeout(t) => Some(*t),
                _ => None,
            })
            .unwrap_or(300)
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
