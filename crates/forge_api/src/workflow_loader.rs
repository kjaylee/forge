use std::path::PathBuf;
use std::sync::Arc;

use forge_app::{FileReadService, Infrastructure};
use forge_domain::Workflow;

pub struct WorkflowLoader<F>(Arc<F>);

impl<F> WorkflowLoader<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self(infra)
    }
}

impl<F: Infrastructure> WorkflowLoader<F> {
    /// loads the workflow from the given path.
    pub async fn load(&self, workflow: PathBuf) -> anyhow::Result<Workflow> {
        let workflow_content = self.0.file_read_service().read(workflow).await?;
        let workflow = toml::from_str(&workflow_content)?;
        Ok(workflow)
    }
}
