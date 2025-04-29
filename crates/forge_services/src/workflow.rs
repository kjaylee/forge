use std::path::Path;
use std::sync::Arc;

use anyhow::Context;
use forge_domain::{Workflow, WorkflowService};
use merge::Merge;

use crate::{FsReadService, Infrastructure};

/// A workflow loader to load the workflow from the given path.
/// It also resolves the internal paths specified in the workflow.
pub struct ForgeWorkflowService<F>(Arc<F>);

impl<F> ForgeWorkflowService<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self(app)
    }
}

impl<F: Infrastructure> ForgeWorkflowService<F> {
    /// Loads the workflow from the given path.
    /// If a path is provided, uses that workflow and merges with defaults
    /// If no path is provided:
    ///   - Loads from current directory's forge.yaml merged with defaults (if
    ///     forge.yaml exists)
    ///   - Falls back to embedded default if forge.yaml doesn't exist
    ///
    /// When merging, the custom workflow values take precedence over defaults.
    pub async fn init(&self, path: Option<&Path>) -> anyhow::Result<Workflow> {
        // Determine the workflow source

        match path {
            // Path was provided
            Some(path) => self.load_and_merge_workflow(path).await,

            // No path provided and no local forge.yaml exists
            None => {
                let path = Path::new("forge.yaml");
                if path.exists() {
                    self.load_and_merge_workflow(path).await
                } else {
                    Ok(Workflow::default())
                }
            }
        }
    }

    /// Loads a workflow from a specific file path and merges it with the
    /// default workflow
    async fn load_and_merge_workflow(&self, path: &Path) -> anyhow::Result<Workflow> {
        // Load the custom workflow
        let content = self.0.file_read_service().read(path).await?;
        let custom_workflow: Workflow = serde_yml::from_str(&content)
            .with_context(|| format!("Failed to parse workflow from {}", path.display()))?;

        // Create a default workflow and merge with the custom one
        let mut merged_workflow = Workflow::default();
        merged_workflow.merge(custom_workflow);
        Ok(merged_workflow)
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> WorkflowService for ForgeWorkflowService<F> {
    async fn init(&self, path: Option<&Path>) -> anyhow::Result<Workflow> {
        self.init(path).await
    }
}
