use forge_domain::{Workflow, WorkflowId, WorkflowRepository, WorkflowState};

pub struct ForgeWorkflowRepository {}

impl ForgeWorkflowRepository {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl WorkflowRepository for ForgeWorkflowRepository {
    async fn get(&self, id: &WorkflowId) -> anyhow::Result<Option<Workflow>> {
        todo!()
    }
    async fn set(&self, workflow: Workflow) -> anyhow::Result<WorkflowId> {
        todo!()
    }
    async fn get_state(&self, id: &WorkflowId) -> anyhow::Result<WorkflowState> {
        todo!()
    }
    async fn set_state(&self, id: &WorkflowId, state: WorkflowState) -> anyhow::Result<()> {
        todo!()
    }
}
