#![allow(dead_code)]

use std::collections::HashSet;

use crate::{Agent, AgentId};

#[derive(Default)]
pub struct Workflow {
    pub agents: Vec<Agent>,
}

impl Workflow {
    pub fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }

    pub fn get_agent(&self, id: &AgentId) -> crate::Result<&Agent> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }

    pub fn find_head(&self) -> Option<&Agent> {
        let downstream_agents = self
            .agents
            .iter()
            .flat_map(|a| a.handovers.iter().map(|h| &h.agent))
            .collect::<HashSet<_>>();

        self.agents
            .iter()
            .find(|a| !downstream_agents.contains(&a.id))
    }

    pub fn get_head(&self) -> crate::Result<&Agent> {
        self.find_head()
            .ok_or_else(|| crate::Error::HeadAgentUndefined)
    }
}
