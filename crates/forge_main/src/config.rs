use anyhow::{anyhow, Result};
use colored::Colorize;
use forge_domain::Environment;
use std::collections::HashMap;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConfigKey {
    PrimaryModel,
    SecondaryModel,
    ToolTimeout,
}

impl ConfigKey {
    fn as_str(&self) -> &'static str {
        match self {
            ConfigKey::PrimaryModel => "primary-model",
            ConfigKey::SecondaryModel => "secondary-model",
            ConfigKey::ToolTimeout => "tool-timeout",
        }
    }
}

impl FromStr for ConfigKey {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "primary-model" => Ok(ConfigKey::PrimaryModel),
            "secondary-model" => Ok(ConfigKey::SecondaryModel),
            "tool-timeout" => Ok(ConfigKey::ToolTimeout),
            _ => Err(anyhow!("Invalid configuration key: {}. Valid keys are: primary-model, secondary-model, tool-timeout", s)),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConfigValue {
    Model(String),
    ToolTimeout(u32),
}

impl ConfigValue {
    pub fn as_str(&self) -> String {
        match self {
            ConfigValue::Model(model) => model.clone(),
            ConfigValue::ToolTimeout(timeout) => timeout.to_string(),
        }
    }

    pub fn from_key_value(key: &ConfigKey, value: &str) -> Result<Self> {
        match key {
            ConfigKey::PrimaryModel | ConfigKey::SecondaryModel => {
                // Add model name validation if needed
                if value.trim().is_empty() {
                    Err(anyhow!("Model name cannot be empty"))
                } else {
                    Ok(ConfigValue::Model(value.to_string()))
                }
            }
            ConfigKey::ToolTimeout => match value.parse::<u32>() {
                Ok(0) => Err(anyhow!("Tool timeout must be greater than 0")),
                Ok(timeout) => Ok(ConfigValue::ToolTimeout(timeout)),
                Err(_) => Err(anyhow!(
                    "Invalid tool timeout value: {}. Must be a positive number.",
                    value
                )),
            },
        }
    }
}

pub struct Config {
    values: HashMap<ConfigKey, ConfigValue>,
}

impl From<&Environment> for Config {
    fn from(env: &Environment) -> Self {
        let mut values = HashMap::new();
        values.insert(
            ConfigKey::PrimaryModel,
            ConfigValue::Model(env.large_model_id.clone()),
        );
        values.insert(
            ConfigKey::SecondaryModel,
            ConfigValue::Model(env.small_model_id.clone()),
        );
        values.insert(ConfigKey::ToolTimeout, ConfigValue::ToolTimeout(20));
        Self { values }
    }
}

impl Config {
    pub fn get(&self, key: &str) -> Option<String> {
        key.parse::<ConfigKey>()
            .ok()
            .and_then(|k| self.values.get(&k))
            .map(|v| v.as_str())
    }

    pub fn insert(&mut self, key: &str, value: &str) -> Result<()> {
        let config_key = ConfigKey::from_str(key)?;
        let config_value = ConfigValue::from_key_value(&config_key, value)?;
        self.values.insert(config_key, config_value);
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn to_display_string(&self) -> String {
        let mut output = String::new();

        output.push_str(&format!("\n{}\n", "Current Configuration:".bold().cyan()));
        output.push_str(&format!("{}\n", "--------------------".dimmed()));

        if self.is_empty() {
            output.push_str(&format!("{}\n", "No configurations set".italic().yellow()));
        } else {
            let mut configs: Vec<_> = self.values.iter().collect();
            configs.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str())); // Sort by key string
            for (key, value) in configs {
                output.push_str(&format!(
                    "{:<20}  {}\n",
                    key.as_str().bright_green(),
                    value.as_str().bright_white()
                ));
            }
        }

        output.push_str(&format!("{}\n", "--------------------".dimmed()));
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    impl Default for Config {
        fn default() -> Self {
            Self { values: HashMap::new() }
        }
    }

    #[test]
    fn test_config_key_from_str() {
        // Valid keys
        assert_eq!(
            ConfigKey::from_str("primary-model").unwrap(),
            ConfigKey::PrimaryModel
        );
        assert_eq!(
            ConfigKey::from_str("secondary-model").unwrap(),
            ConfigKey::SecondaryModel
        );
        assert_eq!(
            ConfigKey::from_str("tool-timeout").unwrap(),
            ConfigKey::ToolTimeout
        );

        // Invalid key
        let err = ConfigKey::from_str("invalid-key").unwrap_err();
        assert!(err.to_string().contains("Invalid configuration key"));
        assert!(err.to_string().contains("primary-model"));
        assert!(err.to_string().contains("secondary-model"));
        assert!(err.to_string().contains("tool-timeout"));
    }

    #[test]
    fn test_config_key_as_str() {
        assert_eq!(ConfigKey::PrimaryModel.as_str(), "primary-model");
        assert_eq!(ConfigKey::SecondaryModel.as_str(), "secondary-model");
        assert_eq!(ConfigKey::ToolTimeout.as_str(), "tool-timeout");
    }

    #[test]
    fn test_config_value_from_key_value() {
        // Test model values
        let model_keys = [ConfigKey::PrimaryModel, ConfigKey::SecondaryModel];
        for key in model_keys {
            // Valid model name
            let value = ConfigValue::from_key_value(&key, "gpt-4").unwrap();
            assert!(matches!(value, ConfigValue::Model(m) if m == "gpt-4"));

            // Empty model name
            let err = ConfigValue::from_key_value(&key, "").unwrap_err();
            assert!(err.to_string().contains("Model name cannot be empty"));

            // Whitespace model name
            let err = ConfigValue::from_key_value(&key, "   ").unwrap_err();
            assert!(err.to_string().contains("Model name cannot be empty"));
        }

        // Test tool timeout
        let key = ConfigKey::ToolTimeout;

        // Valid timeout
        let value = ConfigValue::from_key_value(&key, "30").unwrap();
        assert!(matches!(value, ConfigValue::ToolTimeout(t) if t == 30));

        // Zero timeout
        let err = ConfigValue::from_key_value(&key, "0").unwrap_err();
        assert!(err
            .to_string()
            .contains("Tool timeout must be greater than 0"));

        // Invalid number
        let err = ConfigValue::from_key_value(&key, "abc").unwrap_err();
        assert!(err.to_string().contains("Invalid tool timeout value"));

        // Negative number
        let err = ConfigValue::from_key_value(&key, "-1").unwrap_err();
        assert!(err.to_string().contains("Invalid tool timeout value"));
    }

    #[test]
    fn test_config_value_as_str() {
        assert_eq!(ConfigValue::Model("gpt-4".to_string()).as_str(), "gpt-4");
        assert_eq!(ConfigValue::ToolTimeout(30).as_str(), "30");
    }

    #[test]
    fn test_config_operations() {
        let mut config = Config::default();
        assert!(config.is_empty());

        // Test setting and getting values
        config.insert("primary-model", "gpt-4").unwrap();
        assert_eq!(config.get("primary-model").unwrap(), "gpt-4");

        config.insert("tool-timeout", "30").unwrap();
        assert_eq!(config.get("tool-timeout").unwrap(), "30");

        // Test overwriting values
        config.insert("primary-model", "gpt-3.5-turbo").unwrap();
        assert_eq!(config.get("primary-model").unwrap(), "gpt-3.5-turbo");

        // Test getting non-existent key
        assert!(config.get("non-existent").is_none());

        // Test invalid operations
        assert!(config.insert("invalid-key", "value").is_err());
        assert!(config.insert("tool-timeout", "invalid").is_err());
        assert!(config.insert("tool-timeout", "0").is_err());
    }
}
