use std::path::Path;

use anyhow::Result;
use forge_domain::Workflow;
use forge_services::WorkflowRepository;

pub struct ForgeWorkflowRepository {}

impl Default for ForgeWorkflowRepository {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeWorkflowRepository {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl WorkflowRepository for ForgeWorkflowRepository {
    /// Get the retry configuration for the workflow
    fn get(&self) -> Workflow {
        todo!()
    }

    async fn register(&self, _path: &Path) -> Result<()> {
        todo!()
    }
}