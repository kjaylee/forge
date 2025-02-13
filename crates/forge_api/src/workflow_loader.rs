use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Context;
use anyhow::Result;
use forge_app::{FileReadService, Infrastructure};
use forge_domain::{Prompt, Workflow};

/// A workflow loader to load the workflow from the given path.
/// It also resolves the internal paths specified in the workflow.
pub struct WorkflowLoader<F>(Arc<F>);

impl<F> WorkflowLoader<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self(app)
    }
}

impl<F: Infrastructure> WorkflowLoader<F> {
    /// loads the workflow from the given path.
    pub async fn load(&self, workflow_path: PathBuf) -> anyhow::Result<Workflow> {
        let workflow_content = self
            .0
            .file_read_service()
            .read(workflow_path.clone())
            .await?;
        let workflow: Workflow = toml::from_str(&workflow_content)?;

        let workflow_dir = workflow_path
            .parent()
            .with_context(|| {
                format!(
                    "Failed to get parent directory of workflow file: {:?}",
                    workflow_path
                )
            })?
            .to_path_buf();

        self.resolve(workflow, workflow_dir).await
    }

    /// given an workflow, it resolves all the internal paths specified in workflow.
    async fn resolve(&self, mut workflow: Workflow, path: PathBuf) -> Result<Workflow> {
        for agent in workflow.agents.iter_mut() {
            agent.system_prompt = self.resolve_prompt(&agent.system_prompt, &path).await?;
            agent.user_prompt = self.resolve_prompt(&agent.user_prompt, &path).await?;
        }
        Ok(workflow)
    }

    /// if prompt is a file path, then it reads the file and returns the content.
    /// if the file path is relative, it resolves it with the given path.
    /// otherwise, it returns the prompt as it is.
    async fn resolve_prompt<V: Clone>(
        &self,
        prompt: &Prompt<V>,
        path: &PathBuf,
    ) -> Result<Prompt<V>> {
        if let Some(file_path) = Self::is_file_path(path, prompt.template.as_str()) {
            let abs_path = if file_path.is_absolute() {
                file_path
            } else {
                path.join(file_path)
            };
            Ok(Prompt::new(
                self.0.file_read_service().read(abs_path).await?,
            ))
        } else {
            Ok(prompt.clone())
        }
    }

    /// checks if given content is valid file path by checking it's existance.    
    fn is_file_path(workflow_dir: &PathBuf, content: &str) -> Option<PathBuf> {
        let path = Path::new(content);
        if path.exists() || workflow_dir.join(path).exists() {
            return Some(path.to_path_buf());
        }
        None
    }
}
