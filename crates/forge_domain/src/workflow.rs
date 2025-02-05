use std::collections::{HashMap, HashSet};

use derive_more::derive::{Display, From};

use crate::AgentId;

#[derive(Debug, Display, Eq, PartialEq, Hash, Clone)]
pub struct WorkflowId(String);

pub struct Workflow {
    pub id: WorkflowId,
    pub description: String,
    pub handovers: HashMap<FlowId, Vec<FlowId>>,
}

impl Workflow {
    /// Returns flows that have no predecessors
    pub fn head_flow(&self) -> Vec<FlowId> {
        let values = self
            .handovers
            .values()
            .clone()
            .into_iter()
            .flatten()
            .collect::<HashSet<_>>();

        self.handovers
            .keys()
            .cloned()
            .filter(|flow| !values.contains(flow))
            .collect::<Vec<_>>()
    }
}

#[derive(Debug, Display, Eq, PartialEq, From, Hash, Clone)]
pub enum FlowId {
    Agent(AgentId),
    Workflow(WorkflowId),
}

pub struct Handover {
    pub from: FlowId,
    pub to: FlowId,
}
