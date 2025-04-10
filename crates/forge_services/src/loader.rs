use std::path::Path;
use std::sync::Arc;

use anyhow::Context;
use forge_domain::Workflow;
use merge::Merge;

use crate::infra::{FsReadService, Infrastructure};

// Import the default workflow creation function
const DEFAULT_YAML: &str = include_str!("../../../forge.default.yaml");

/// Represents the possible sources of a workflow configuration
enum WorkflowSource<'a> {
    /// Explicitly provided path
    ExplicitPath(&'a Path),
    /// Default configuration embedded in the binary
    Default,
    /// Project-specific configuration in the current directory
    ProjectConfig,
}

/// A workflow loader to load the workflow from the given path.
/// It also resolves the internal paths specified in the workflow.
pub struct ForgeLoaderService<F>(Arc<F>);

impl<F> ForgeLoaderService<F> {
    pub fn new(app: Arc<F>) -> Self {
        Self(app)
    }
}

impl<F: Infrastructure> ForgeLoaderService<F> {
    /// Loads the workflow from the given path.
    /// If a path is provided, uses that workflow directly without merging.
    /// If no path is provided:
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
            WorkflowSource::Default => {
                // Use the default workflow from the embedded YAML
                let workflow: Workflow = serde_yaml::from_str(DEFAULT_YAML)
                    .expect("Failed to parse default forge.yaml configuration");
                Ok(workflow)
            }
            WorkflowSource::ProjectConfig => self.load_with_project_config().await,
        }
    }

    /// Loads a workflow from a specific file path
    async fn load_from_explicit_path(&self, path: &Path) -> anyhow::Result<Workflow> {
        // Get a reference to the file read service
        let fs_read = self.0.file_read_service();

        // Read the file content
        let bytes = fs_read
            .read(path)
            .await
            .with_context(|| format!("Failed to read workflow file from {}", path.display()))?;

        // Convert bytes to string
        let content = String::from_utf8(bytes.to_vec()).with_context(|| {
            format!(
                "Failed to convert file content to UTF-8 from {}",
                path.display()
            )
        })?;

        // Parse the YAML content into a Workflow
        let workflow: Workflow = serde_yaml::from_str(&content)
            .with_context(|| format!("Failed to parse workflow from {}", path.display()))?;

        Ok(workflow)
    }

    /// Loads workflow by merging project config with default workflow
    async fn load_with_project_config(&self) -> anyhow::Result<Workflow> {
        let project_path = Path::new("forge.yaml").canonicalize()?;

        // Get a reference to the file read service
        let fs_read = self.0.file_read_service();

        // Read the project file
        let bytes = fs_read
            .read(project_path.as_path())
            .await
            .with_context(|| {
                format!(
                    "Failed to read project workflow from {}",
                    project_path.display()
                )
            })?;

        // Convert bytes to string
        let project_content = String::from_utf8(bytes.to_vec())
            .with_context(|| "Failed to convert project file content to UTF-8".to_string())?;

        // Parse the YAML content into a Workflow
        let project_workflow: Workflow =
            serde_yaml::from_str(&project_content).with_context(|| {
                format!(
                    "Failed to parse project workflow: {}",
                    project_path.display()
                )
            })?;

        // Merge workflows with project taking precedence
        // Use the default workflow from the embedded YAML
        let mut merged_workflow: Workflow = serde_yaml::from_str(DEFAULT_YAML)
            .expect("Failed to parse default forge.yaml configuration");
        merged_workflow.merge(project_workflow);

        Ok(merged_workflow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_yaml_loads_correctly() {
        // This test ensures that the default YAML can be parsed into a Workflow
        let workflow: Workflow = serde_yaml::from_str(DEFAULT_YAML)
            .expect("Failed to parse default forge.yaml configuration");

        // Basic sanity checks
        assert!(
            !workflow.agents.is_empty(),
            "Default workflow should have agents"
        );

        // Check that we have the software-engineer agent
        let has_engineer = workflow
            .agents
            .iter()
            .any(|agent| agent.id.to_string() == "software-engineer");
        assert!(
            has_engineer,
            "Default workflow should have the software-engineer agent"
        );
    }
}
