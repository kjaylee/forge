use std::collections::HashMap;

use merge::Merge;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{Agent, AgentId};

fn merge_agents(base: &mut Vec<Agent>, other: Vec<Agent>) {
    for other_agent in other {
        if let Some(base_agent) = base.iter_mut().find(|a| a.id == other_agent.id) {
            // If the base contains an agent with the same ID, merge them
            base_agent.merge(other_agent);
        } else {
            // Otherwise, append the other agent to the base list
            base.push(other_agent);
        }
    }
}

#[derive(Default, Debug, Clone, Serialize, Deserialize, Merge)]
pub struct Workflow {
    #[merge(strategy = merge_agents)]
    pub agents: Vec<Agent>,
    pub variables: Option<HashMap<String, Value>>,
}

impl Workflow {
    fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents
            .iter()
            .filter(|a| a.enable)
            .find(|a| a.id == *id)
    }

    pub fn get_agent(&self, id: &AgentId) -> crate::Result<&Agent> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }
}
