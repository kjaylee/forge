#![allow(dead_code)]

use crate::variables::Variables;
use crate::{Agent, AgentId, Workflow, WorkflowId};

#[async_trait::async_trait]
pub trait AgentExecutor {
    async fn execute(&self, agent: &Agent) -> anyhow::Result<Variables>;
}

#[derive(Default)]
pub struct Arena {
    pub agents: Vec<Agent>,
    // TODO: Workflows should be stored in a Hashmap to improve lookup performance
    pub workflows: Vec<Workflow>,
}

impl Arena {
    pub fn find_agent(&self, id: &AgentId) -> Option<&Agent> {
        self.agents.iter().find(|a| a.id == *id)
    }

    pub fn find_workflow(&self, id: &WorkflowId) -> Option<&Workflow> {
        self.workflows.iter().find(|w| w.id == *id)
    }

    pub fn get_workflow(&self, id: &WorkflowId) -> Result<&Workflow, crate::Error> {
        self.find_workflow(id)
            .ok_or_else(|| crate::Error::WorkflowUndefined(id.clone()))
    }

    pub fn get_agent(&self, id: &AgentId) -> Result<&Agent, crate::Error> {
        self.find_agent(id)
            .ok_or_else(|| crate::Error::AgentUndefined(id.clone()))
    }
}
