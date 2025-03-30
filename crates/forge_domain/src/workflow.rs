use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{Agent, AgentId};

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option, into)]
pub struct ModeConfig {
    #[merge(strategy = crate::merge::std::overwrite)]
    pub name: String,

    #[merge(strategy = crate::merge::std::overwrite)]
    pub description: String,

    #[merge(strategy = crate::merge::std::overwrite)]
    pub command: String,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Workflow {
    #[merge(strategy = crate::merge::vec::unify_by_key)]
    pub agents: Vec<Agent>,

    #[merge(strategy = crate::merge::option)]
    pub variables: Option<HashMap<String, Value>>,

    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub commands: Vec<Command>,

    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub modes: Vec<ModeConfig>,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option, into)]
pub struct Command {
    #[merge(strategy = crate::merge::std::overwrite)]
    pub name: String,

    #[merge(strategy = crate::merge::std::overwrite)]
    pub description: String,

    #[merge(strategy = crate::merge::option)]
    pub value: Option<String>,
}

impl Workflow {
    fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }

    pub fn get_agent(&self, id: &AgentId) -> crate::Result<&Agent> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }

    pub fn find_mode(&self, name: &str) -> Option<&ModeConfig> {
        let name_upper = name.to_uppercase();
        self.modes
            .iter()
            .find(|m| m.name.to_uppercase() == name_upper)
    }
}
