use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::template::Template;
use crate::{SystemContext, ToolName};

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq, Hash)]
#[serde(transparent)]
pub struct Mode(String);

impl Mode {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into().to_lowercase())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn is_act(&self) -> bool {
        self.0 == "act"
    }

    pub fn is_plan(&self) -> bool {
        self.0 == "plan"
    }
}

impl Default for Mode {
    fn default() -> Self {
        Self("act".to_string())
    }
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.to_uppercase())
    }
}

impl From<&str> for Mode {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<String> for Mode {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

/// Configuration for a specific mode (Act or Plan)
#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct ModeConfig {
    /// Tools available in this mode
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub tools: Option<Vec<ToolName>>,

    /// System prompt template for this mode
    #[serde(skip_serializing_if = "Option::is_none")]
    #[merge(strategy = crate::merge::option)]
    pub system_prompt: Option<Template<SystemContext>>,
}

impl Default for ModeConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl ModeConfig {
    /// Creates a new empty mode configuration
    pub fn new() -> Self {
        Self { tools: None, system_prompt: None }
    }
}

/// A newtype wrapper around HashMap<Mode, ModeConfig> to provide additional functionality
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ModeDefinitions(HashMap<Mode, ModeConfig>);

impl ModeDefinitions {
    /// Creates a new empty ModeDefinitions
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    /// Get a reference to the ModeConfig for the specified mode, if it exists
    pub fn get(&self, mode: &Mode) -> Option<&ModeConfig> {
        self.0.get(mode)
    }

    /// Get a mutable reference to the ModeConfig for the specified mode
    /// If the mode doesn't exist, it will be created with a default ModeConfig
    pub fn get_mut_or_default(&mut self, mode: Mode) -> &mut ModeConfig {
        self.0.entry(mode).or_insert_with(ModeConfig::new)
    }

    /// Insert a ModeConfig for the specified mode
    pub fn insert(&mut self, mode: Mode, config: ModeConfig) -> Option<ModeConfig> {
        self.0.insert(mode, config)
    }

    /// Returns an iterator over all mode configurations
    pub fn iter(&self) -> impl Iterator<Item = (&Mode, &ModeConfig)> {
        self.0.iter()
    }

    /// Returns a mutable iterator over all mode configurations
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&Mode, &mut ModeConfig)> {
        self.0.iter_mut()
    }
}

impl Deref for ModeDefinitions {
    type Target = HashMap<Mode, ModeConfig>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ModeDefinitions {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<HashMap<Mode, ModeConfig>> for ModeDefinitions {
    fn from(map: HashMap<Mode, ModeConfig>) -> Self {
        Self(map)
    }
}

impl From<ModeDefinitions> for HashMap<Mode, ModeConfig> {
    fn from(definitions: ModeDefinitions) -> Self {
        definitions.0
    }
}
