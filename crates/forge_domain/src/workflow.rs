use crate::AgentId;

pub struct WorkflowId(String);

pub struct Workflow {
    pub id: WorkflowId,
    pub description: String,
    pub handovers: Vec<Handover>,
}

pub enum FlowId {
    Agent(AgentId),
    Workflow(WorkflowId),
}

pub struct Handover {
    pub from: FlowId,
    pub to: FlowId,
}
