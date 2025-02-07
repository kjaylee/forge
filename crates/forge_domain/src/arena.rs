#![allow(dead_code)]

use crate::variables::Variables;
use crate::{Agent, AgentId, Workflow};

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
}
