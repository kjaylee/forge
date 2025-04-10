use std::collections::HashMap;

use derive_setters::Setters;
use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::workflow_config::WorkflowConfig;
use crate::{Agent, AgentId, ModelId};

// Include the default yaml configuration file as a string
const DEFAULT_YAML: &str = include_str!("../../../forge.default.yaml");

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Setters)]
#[setters(strip_option)]
pub struct Workflow {
    #[merge(strategy = crate::merge::vec::unify_by_key)]
    pub agents: Vec<Agent>,

    #[merge(strategy = crate::merge::option)]
    pub variables: Option<HashMap<String, Value>>,

    #[merge(strategy = crate::merge::vec::append)]
    #[serde(default)]
    pub commands: Vec<Command>,

    #[merge(strategy = crate::merge::option)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<ModelId>,
}

impl Default for Workflow {
    fn default() -> Self {
        // Parse the YAML string into a Workflow struct
        let workflow: Workflow = serde_yaml::from_str(DEFAULT_YAML)
            .expect("Failed to parse default forge.yaml configuration");

        workflow
    }
}

impl From<WorkflowConfig> for Workflow {
    fn from(config: WorkflowConfig) -> Self {
        let workflow = Workflow::default();
        // FIXME: need to merge config settings into workflow
        todo!();
        workflow
    }
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
}
