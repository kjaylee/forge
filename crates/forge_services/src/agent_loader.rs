use std::path::Path;
use std::sync::Arc;

use anyhow::{Context, Result};
use forge_app::domain::{Agent, AgentId, Workflow};
use forge_domain::Environment;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::{FileReaderInfra, FileWriterInfra};

/// A service for loading agent definitions from individual files in the
/// forge/agent directory
pub struct AgentLoaderService<F> {
    infra: Arc<F>,
    environment: Environment,
}

/// Represents the frontmatter structure of an agent definition file
#[derive(Debug, Clone, Serialize, Deserialize)]
struct AgentFrontmatter {
    #[serde(flatten)]
    agent: Agent,
}

/// Represents a complete agent definition with frontmatter and markdown content
#[derive(Debug, Clone)]
pub struct AgentDefinitionFile {
    pub agent: Agent,
    pub content: String,
}

impl<F> AgentLoaderService<F> {
    pub fn new(infra: Arc<F>, environment: Environment) -> Self {
        Self { infra, environment }
    }
}

impl<F: FileReaderInfra + FileWriterInfra> AgentLoaderService<F> {
    /// Load all agent definitions from the forge/agent directory
    pub async fn load_agents(&self) -> Result<Vec<AgentDefinitionFile>> {
        let agent_dir = self.environment.agent_path();

        if !agent_dir.exists() {
            return Ok(Vec::new());
        }

        let mut agents = Vec::new();
        let entries = std::fs::read_dir(&agent_dir)
            .with_context(|| format!("Failed to read agent directory: {}", agent_dir.display()))?;

        for entry in entries {
            let entry = entry?;
            let path = entry.path();

            // Only process .md files
            if path.extension().and_then(|s| s.to_str()) == Some("md")
                && let Ok(agent_def) = self.parse_agent_file(&path).await
            {
                agents.push(agent_def)
            }
        }

        Ok(agents)
    }

    /// Parse an individual agent definition file with YAML frontmatter
    async fn parse_agent_file(&self, path: &Path) -> Result<AgentDefinitionFile> {
        let content = self
            .infra
            .read_utf8(path)
            .await
            .with_context(|| format!("Failed to read agent file: {}", path.display()))?;

        // Split frontmatter and markdown content
        let (frontmatter_str, markdown_content) = if content.starts_with("---") {
            let mut parts = content.splitn(3, "---");
            parts.next(); // Skip the first empty part
            let frontmatter = parts
                .next()
                .ok_or_else(|| anyhow::anyhow!("Missing frontmatter in {}", path.display()))?;
            let markdown = parts.next().unwrap_or("");
            (frontmatter, markdown)
        } else {
            return Err(anyhow::anyhow!(
                "No YAML frontmatter found in {}",
                path.display()
            ));
        };

        // Parse the frontmatter
        let frontmatter: AgentFrontmatter = serde_yml::from_str(frontmatter_str)
            .with_context(|| format!("Failed to parse YAML frontmatter in {}", path.display()))?;

        // Use the filename (without extension) as the agent ID if not specified
        let mut agent = frontmatter.agent;
        if agent.id == AgentId::default() {
            let filename = path
                .file_stem()
                .and_then(|s| s.to_str())
                .ok_or_else(|| anyhow::anyhow!("Invalid filename: {}", path.display()))?;
            agent.id = AgentId::new(filename);
        }

        Ok(AgentDefinitionFile { agent, content: markdown_content.trim().to_string() })
    }

    /// Enhance workflow with loaded agents
    pub async fn extend(&self, mut workflow: Workflow) -> Result<Workflow> {
        let agent_definitions = self.load_agents().await?;
        merge_agents_into_workflow(&mut workflow, agent_definitions);
        Ok(workflow)
    }
}

/// Merge loaded agents into an existing workflow
pub fn merge_agents_into_workflow(
    workflow: &mut Workflow,
    agent_definitions: Vec<AgentDefinitionFile>,
) {
    for agent_def in agent_definitions {
        // Check if an agent with this ID already exists in the workflow
        if let Some(existing_agent) = workflow
            .agents
            .iter_mut()
            .find(|a| a.id == agent_def.agent.id)
        {
            // Merge the loaded agent into the existing one
            existing_agent.merge(agent_def.agent);
        } else {
            // Add the new agent to the workflow
            workflow.agents.push(agent_def.agent);
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_merge_agents_into_workflow() {
        let mut workflow = Workflow::new();

        // Add an existing agent to the workflow
        let existing_agent = Agent::new(AgentId::new("existing-agent"))
            .title("Existing Agent".to_string())
            .description("Original description".to_string());
        workflow.agents.push(existing_agent);

        let agent_definitions = vec![
            AgentDefinitionFile {
                agent: Agent::new(AgentId::new("new-agent"))
                    .title("New Agent".to_string())
                    .description("A new agent".to_string()),
                content: "New agent content".to_string(),
            },
            AgentDefinitionFile {
                agent: Agent::new(AgentId::new("existing-agent"))
                    .description("Updated description".to_string()),
                content: "Updated content".to_string(),
            },
        ];

        merge_agents_into_workflow(&mut workflow, agent_definitions);

        assert_eq!(workflow.agents.len(), 2);

        // Check that the new agent was added
        let new_agent = workflow
            .agents
            .iter()
            .find(|a| a.id == AgentId::new("new-agent"))
            .unwrap();
        assert_eq!(new_agent.title, Some("New Agent".to_string()));

        // Check that the existing agent was updated
        let updated_agent = workflow
            .agents
            .iter()
            .find(|a| a.id == AgentId::new("existing-agent"))
            .unwrap();
        assert_eq!(
            updated_agent.description,
            Some("Updated description".to_string())
        );
        assert_eq!(updated_agent.title, Some("Existing Agent".to_string())); // Should retain original title
    }
}
