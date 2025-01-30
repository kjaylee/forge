use crate::{Agent, AgentId};

pub struct JobId(String);

pub struct Job {
    pub id: JobId,
    pub name: String,
    pub agent: AgentId,
    pub handover: Handover,
}

pub struct Handover {
    pub jobs: Vec<JobId>,
    pub max: usize,
    pub min: usize,
}

pub struct Workflow {
    pub jobs: Vec<Job>,
}

