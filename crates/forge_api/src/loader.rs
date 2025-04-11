use std::path::Path;
use std::sync::Arc;

use anyhow::Context;
use forge_domain::Workflow;
use forge_services::{FsReadService, Infrastructure};

/// Represents the possible sources of a workflow configuration
enum WorkflowSource<'a> {
    /// Explicitly provided path
    ExplicitPath(&'a Path),
    /// Default configuration embedded in the binary
    Default,
    /// Project-specific configuration in the current directory
    ProjectConfig,
}

/// A workflow loader to load the workflow config from the given path.
/// It also resolves the internal paths specified in the workflow config.
pub struct ForgeLoaderService<F>(Arc<F>);

impl<F> ForgeLoaderService<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self(app)
    }
}

impl<F: Infrastructure> ForgeLoaderService<F> {
    /// Loads the workflow config from the given path.
    /// If a path is provided, uses that workflow config directly without
    /// merging. If no path is provided:
    ///   - Loads from current directory's forge.yaml merged with defaults (if
    ///     forge.yaml exists)
    ///   - Falls back to embedded default if forge.yaml doesn't exist
    ///
    /// When merging, the project's forge.yaml values take precedence over
    /// defaults.
    pub async fn load(&self, path: Option<&Path>) -> anyhow::Result<Workflow> {
        // Determine the workflow source
        let source = match path {
            Some(path) => WorkflowSource::ExplicitPath(path),
            None if Path::new("forge.yaml").exists() => WorkflowSource::ProjectConfig,
            None => WorkflowSource::Default,
        };

        // Load the workflow based on its source
        match source {
            WorkflowSource::ExplicitPath(path) => self.load_from_explicit_path(path).await,
            WorkflowSource::Default => Ok(Workflow::default()),
            WorkflowSource::ProjectConfig => self.load_with_project_config().await,
        }
    }

    /// Loads a workflow config from a specific file path
    async fn load_from_explicit_path(&self, path: &Path) -> anyhow::Result<Workflow> {
        let content = String::from_utf8(self.0.file_read_service().read(path).await?.to_vec())?;
        let workflow_config: Workflow = serde_yaml::from_str(&content)
            .with_context(|| format!("Failed to parse workflow config from {}", path.display()))?;
        Ok(workflow_config)
    }

    /// Loads workflow config by merging project config with default workflow
    /// config
    async fn load_with_project_config(&self) -> anyhow::Result<Workflow> {
        let project_path = Path::new("forge.yaml").canonicalize()?;

        let project_content = String::from_utf8(
            self.0
                .file_read_service()
                .read(project_path.as_path())
                .await?
                .to_vec(),
        )?;

        let project_config: Workflow =
            serde_yaml::from_str(&project_content).with_context(|| {
                format!(
                    "Failed to parse project workflow config: {}",
                    project_path.display()
                )
            })?;

        Ok(project_config)
    }
}
