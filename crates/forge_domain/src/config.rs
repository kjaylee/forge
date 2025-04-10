use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::temperature::Temperature;
use crate::{Command, ModelId};

/// Configuration for a workflow that contains all settings
/// required to initialize a workflow.
#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Config {
    /// Variables that can be used in templates
    #[merge(strategy = crate::merge::option)]
    pub variables: Option<HashMap<String, Value>>,

    /// Commands that can be used to interact with the workflow
    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub commands: Vec<Command>,

    /// Default model ID to use for agents in this workflow
    #[merge(strategy = crate::merge::option)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<ModelId>,

    /// Maximum depth to which the file walker should traverse for all agents
    /// If not provided, each agent's individual setting will be used
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub max_walker_depth: Option<usize>,

    /// A set of custom rules that all agents should follow
    /// These rules will be applied in addition to each agent's individual rules
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub custom_rules: Option<String>,

    /// Temperature used for all agents
    ///
    /// Temperature controls the randomness in the model's output.
    /// - Lower values (e.g., 0.1) make responses more focused, deterministic,
    ///   and coherent
    /// - Higher values (e.g., 0.8) make responses more creative, diverse, and
    ///   exploratory
    /// - Valid range is 0.0 to 2.0
    /// - If not specified, each agent's individual setting or the model
    ///   provider's default will be used
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub temperature: Option<Temperature>,
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use serde_json::json;

    use super::*;

    #[test]
    fn test_temperature_validation() {
        // Valid temperature values should deserialize correctly
        let valid_temps = [0.0, 0.5, 1.0, 1.5, 2.0];
        for temp in valid_temps {
            let json = json!({
                "temperature": temp
            });

            let config: std::result::Result<Config, serde_json::Error> =
                serde_json::from_value(json);
            assert!(
                config.is_ok(),
                "Valid temperature {} should deserialize",
                temp
            );
            assert_eq!(config.unwrap().temperature.unwrap().value(), temp);
        }

        // Invalid temperature values should fail deserialization
        let invalid_temps = [-0.1, 2.1, 3.0, -1.0, 10.0];
        for temp in invalid_temps {
            let json = json!({
                "temperature": temp
            });

            let config: std::result::Result<Config, serde_json::Error> =
                serde_json::from_value(json);
            assert!(
                config.is_err(),
                "Invalid temperature {} should fail deserialization",
                temp
            );
            let err = config.unwrap_err().to_string();
            assert!(
                err.contains("temperature must be between 0.0 and 2.0"),
                "Error should mention valid range: {}",
                err
            );
        }
    }
}
