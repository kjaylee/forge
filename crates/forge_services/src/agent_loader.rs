use std::path::PathBuf;
use std::sync::Arc;

use anyhow::{Context, Result};
use forge_app::domain::{Agent, AgentId, Workflow};
use forge_domain::Environment;
use forge_walker::Walker;
use gray_matter::Matter;
use gray_matter::engine::YAML;
use merge::Merge;
use serde::{Deserialize, Serialize};

use crate::{FileInfoInfra, FileReaderInfra, FileWriterInfra};

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

impl<F: FileReaderInfra + FileWriterInfra + FileInfoInfra> AgentLoaderService<F> {
    /// Load all agent definitions from the forge/agent directory
    pub async fn load_agents(&self) -> Result<Vec<AgentDefinitionFile>> {
        let agent_dir = self.environment.agent_path();
        if !self.infra.exists(&agent_dir).await? {
            return Ok(vec![]);
        }

        let mut agents = vec![];
        let entries = Walker::min_all()
            .cwd(agent_dir.clone())
            .get()
            .await
            .with_context(|| "Failed to read agent directory")?;

        for entry in entries {
            let path = agent_dir.join(entry.path);

            // Only process .md files
            if entry.file_name.map(|v| v.ends_with(".md")).unwrap_or(false) {
                let agent_def = self.parse_agent_file(path).await?;
                agents.push(agent_def)
            }
        }

        Ok(agents)
    }

    /// Parse an individual agent definition file with YAML frontmatter
    async fn parse_agent_file(&self, path: PathBuf) -> Result<AgentDefinitionFile> {
        let content = self
            .infra
            .read_utf8(&path)
            .await
            .with_context(|| format!("Failed to read agent file: {}", path.display()))?;

        // Parse the frontmatter using gray_matter with type-safe deserialization
        let matter = Matter::<YAML>::new();
        let result = matter
            .parse::<AgentFrontmatter>(&content)
            .with_context(|| format!("Failed to parse YAML frontmatter in {}", path.display()))?;

        // Extract the frontmatter
        let frontmatter = result
            .data
            .context(format!("No YAML frontmatter found in {}", path.display()))?;

        // Use the filename (without extension) as the agent ID if not specified
        let mut agent = frontmatter.agent;
        if agent.id == AgentId::default() {
            let filename = path
                .file_stem()
                .and_then(|s| s.to_str())
                .ok_or_else(|| anyhow::anyhow!("Invalid filename: {}", path.display()))?;
            agent.id = AgentId::new(filename);
        }

        Ok(AgentDefinitionFile { agent, content: result.content.trim().to_string() })
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
