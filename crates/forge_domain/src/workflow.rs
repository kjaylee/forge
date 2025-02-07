use std::collections::HashMap;

use derive_more::derive::{Display, From};

use crate::{AgentId, ToolName};

#[derive(Debug, Display, Eq, PartialEq, Hash, Clone)]
pub struct WorkflowId(String);

pub struct Workflow {
    pub id: WorkflowId,
    pub description: String,
    pub handovers: HashMap<FlowId, Vec<Downstream>>,
    pub head_flow: FlowId,
}

pub struct Downstream {
    pub flow_id: FlowId,
    pub wait: bool,
}

#[derive(Debug, Display, Eq, PartialEq, From, Hash, Clone)]
pub enum FlowId {
    Agent(AgentId),
    Workflow(WorkflowId),
}

impl From<ToolName> for WorkflowId {
    fn from(value: ToolName) -> Self {
        Self(value.into_string())
    }
}
