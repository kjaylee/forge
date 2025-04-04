use std::collections::HashMap;

use serde::{Deserialize, Serialize};

/// Represents the configuration stored in a `.forge` file
#[derive(Debug, Default, Deserialize, Serialize, Clone, PartialEq)]
pub struct ForgeConfig {
    /// Model mappings for different roles
    #[serde(skip_serializing_if = "Option::is_none")]
    pub models: Option<HashMap<String, String>>,
    // Can be extended with other settings in the future
}
