use forge_domain::{Agent, Workflow};

pub struct Orchestrator<'a, S, U, API> {
    workflow: Workflow,
    agents: Vec<Agent<S, U>>,
    api: &'a API,
}
