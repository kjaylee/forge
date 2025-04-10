use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{Command, ModelId};

/// Configuration for a workflow that contains all settings
/// required to initialize a workflow.
#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct WorkflowConfig {
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
}
