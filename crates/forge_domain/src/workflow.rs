use std::collections::{HashMap, HashSet};

use derive_more::derive::{Display, From};

use crate::AgentId;

#[derive(Debug, Display, Eq, PartialEq, Hash, Clone)]
pub struct WorkflowId(String);

pub struct Workflow {
    pub id: WorkflowId,
    pub description: String,
    pub handovers: HashMap<FlowId, Vec<FlowId>>,
    pub head_flow: FlowId,
}

#[derive(Debug, Display, Eq, PartialEq, From, Hash, Clone)]
pub enum FlowId {
    Agent(AgentId),
    Workflow(WorkflowId),
}
