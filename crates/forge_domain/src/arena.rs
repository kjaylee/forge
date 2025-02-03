use std::collections::HashMap;

use petgraph::graph::DiGraph;

use crate::{
    Agent, AgentId, FlowId, Handover, Model, Provider, Schema, ToolName, Variables, Workflow,
    WorkflowId,
};

pub enum Error {}

pub type Result<A> = std::result::Result<A, Error>;

#[async_trait::async_trait]
pub trait AgentExecutor {
    async fn execute(&self, agent: &Agent) -> anyhow::Result<Variables>;
}

pub struct Arena {
    pub agents: Vec<Agent>,
    pub workflows: Option<Vec<Workflow>>,
    pub tools: Option<Vec<SmartTool<Variables>>>,
}

pub struct SmartTool<S> {
    pub name: ToolName,
    pub description: String,
    pub run: FlowId,
    pub input: Schema<S>,
}

pub struct ArenaExecutor {
    arena: Arena,
    graph: DiGraph<FlowId, Handover>,
    entry_point: FlowId,
    agent_index: HashMap<AgentId, Agent>,
    workflow_index: HashMap<WorkflowId, Workflow>,
}

impl ArenaExecutor {
    pub fn new(arena: Arena) -> Self {
        todo!("Create directed graph");
        todo!("Identify entry point");
    }

    pub fn execute(&self, variables: Variables) -> Result<Variables> {
        // - Identify entry point routine
        todo!()
    }
}
