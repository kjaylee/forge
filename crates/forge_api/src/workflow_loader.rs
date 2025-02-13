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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use anyhow::{Context, Result};
    use forge_domain::{ModelId, Workflow};
    use forge_infra::TestInfra;
    use tempfile::tempdir;

    use super::WorkflowLoader;

    struct Fixture {
        _temp_dir: tempfile::TempDir,
        loader: WorkflowLoader<TestInfra>,
    }

    impl Default for Fixture {
        fn default() -> Self {
            let temp_dir = tempdir().unwrap();
            let loader = WorkflowLoader::new(Arc::new(TestInfra::new(
                ModelId::new("anthropic/claude-3.5-sonnet"),
                ModelId::new("anthropic/claude-3.5-sonnet"),
            )));
            Self { _temp_dir: temp_dir, loader }
        }
    }

    impl Fixture {
        /// gives the path of the temp directory.
        fn path(&self) -> &std::path::Path {
            self._temp_dir.path()
        }

        /// creates an path within the temp directory.
        async fn create_file(&self, content: &str, path: &str) -> Result<()> {
            let file_path = self.path().join(path);
            if let Some(parent) = file_path.parent() {
                tokio::fs::create_dir_all(parent).await.with_context(|| {
                    format!("Failed to create directory: {:?}", parent)
                })?;
            }
            tokio::fs::write(&file_path, content).await.with_context(|| {
                format!("Failed to write file: {:?}", file_path)
            })?;
            Ok(())
        }

        /// writes the workflow content to the workflow file and loads it.
        async fn run(&self, workflow: &str) -> Result<Workflow> {
            let workflow_path = self.path().join("workflow.toml");
            tokio::fs::write(&workflow_path, workflow).await?;
            self.loader.load(workflow_path).await
        }
    }

    #[tokio::test]
    async fn test_load_workflow_with_string_literals() {
        let workflow_content = r#"
[[agents]]
id = "developer"
model = "anthropic/claude-3.5-sonnet"
tools = ["tool_forge_fs_read", "tool_forge_fs_create"]
subscribe = ["user_task"]
max_turns = 1024

[agents.system_prompt]
template = "You are a software developer assistant"

[agents.user_prompt]
template = "<task>{{event.value}}</task>"
"#;

        let fixture = Fixture::default();
        let workflow = fixture.run(workflow_content).await.unwrap();
        insta::assert_snapshot!(serde_json::to_string_pretty(&workflow).unwrap());
    }

    #[tokio::test]
    async fn test_load_workflow_with_string_literal_and_path() {
        let workflow_content = r#"
[[agents]]
id = "developer"
model = "anthropic/claude-3.5-sonnet"
tools = ["tool_forge_fs_read", "tool_forge_fs_create"]
subscribe = ["user_task"]
max_turns = 1024

[agents.system_prompt]
template = "./nested/system_prompt.md"

[agents.user_prompt]
template = "<task>{{event.value}}</task>"
"#;

        let system_prompt = r#"You are a software developer assistant, good at solving complex software engineering problems"#;
        let fixture = Fixture::default();

        // creates an system prompt file
        fixture
            .create_file(&system_prompt, "nested/system_prompt.md")
            .await
            .unwrap();

        let workflow = fixture.run(workflow_content).await.unwrap();
        insta::assert_snapshot!(serde_json::to_string_pretty(&workflow).unwrap());
    }

    #[tokio::test]
    async fn test_load_workflow_when_template_path_not_present() {
        let workflow_content = r#"
[[agents]]
id = "developer"
model = "anthropic/claude-3.5-sonnet"
tools = ["tool_forge_fs_read", "tool_forge_fs_create"]
subscribe = ["user_task"]
max_turns = 1024

[agents.system_prompt]
template = "./nested/system_prompt.md"

[agents.user_prompt]
template = "<task>{{event.value}}</task>"
"#;

        let fixture = Fixture::default();
        let workflow = fixture.run(workflow_content).await.unwrap();
        insta::assert_snapshot!(serde_json::to_string_pretty(&workflow).unwrap());
    }
}
