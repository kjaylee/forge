use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::template::Template;
use crate::{SystemContext, ToolName};

#[derive(Debug, Clone, Default, Deserialize, Serialize, PartialEq, Eq, Hash)]
#[serde(rename_all = "snake_case")]
pub enum Mode {
    Plan,
    #[default]
    Act,
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Mode::Plan => write!(f, "PLAN"),
            Mode::Act => write!(f, "ACT"),
        }
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

impl ModeConfig {
    /// Creates a new empty mode configuration
    pub fn new() -> Self {
        Self { tools: None, system_prompt: None }
    }
}
