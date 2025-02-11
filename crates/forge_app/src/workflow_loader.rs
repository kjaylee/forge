use anyhow::{Context, Result};
use forge_domain::{
    Agent, AgentBuilder, AgentId, ModelId, Prompt, SystemContext, ToolName, Variables, Workflow,
};
use serde::{Deserialize, Deserializer};
use std::path::{Path, PathBuf};

#[derive(Debug, Deserialize)]
struct WorkflowConfig {
    id: String,
    agents: Vec<AgentConfig>,
}

#[derive(Debug, Deserialize)]
struct AgentConfig {
    id: String,
    entry: Option<bool>,
    ephemeral: Option<bool>,
    model: ModelId,
    description: String,
    #[serde(deserialize_with = "deserialize_prompt")]
    user_prompt: String,
    #[serde(deserialize_with = "deserialize_prompt")]
    system_prompt: String,
    max_turns: Option<u64>,
    tools: Vec<ToolName>,
}

fn deserialize_prompt<'de, D>(deserializer: D) -> std::result::Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    use serde::de::Error;
    let s = String::deserialize(deserializer)?;
    let path = PathBuf::from(&s);

    // read it right away if it's a file path else defaults to normal text.
    if path.exists() && path.is_file() {
        std::fs::read_to_string(&path).map_err(|e| {
            D::Error::custom(format!(
                "Failed to read prompt file {}: {}",
                path.display(),
                e
            ))
        })
    } else {
        Ok(s)
    }
}

impl TryFrom<AgentConfig> for Agent {
    type Error = anyhow::Error;

    fn try_from(value: AgentConfig) -> Result<Self, Self::Error> {
        let mut builder = AgentBuilder::default()
            .id(AgentId::new(&value.id))
            .model(value.model.clone())
            .description(&value.description)
            .user_prompt(Prompt::<Variables>::new(&value.user_prompt))
            .system_prompt(Prompt::<SystemContext>::new(&value.system_prompt))
            .tools(value.tools.clone());

        if let Some(entry) = value.entry {
            builder = builder.entry(entry);
        }
        if let Some(ephemeral) = value.ephemeral {
            builder = builder.ephemeral(ephemeral);
        }

        if let Some(max_turns) = value.max_turns {
            builder = builder.max_turns(max_turns);
        }

        builder.build().context("Failed to build agent")
    }
}

pub struct WorkflowLoader;

impl WorkflowLoader {
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Workflow> {
        let content =
            std::fs::read_to_string(path).context("Failed to read workflow configuration file")?;

        let config: WorkflowConfig =
            serde_yaml::from_str(&content).context("Failed to parse workflow configuration")?;

        let agents = config
            .agents
            .into_iter()
            .map(|agent_config| Agent::try_from(agent_config))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Workflow::new(agents))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_load_workflow() {
        let workflow_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/forge-workflow.yml");
        let workflows = WorkflowLoader::load(workflow_path).unwrap();

        // Verify title generator agent
        let title_agent = workflows
            .agents
            .iter()
            .find(|a| a.id.as_str() == "title-generator")
            .expect("Title generator agent not found");

        assert_eq!(
            title_agent.description,
            "Generates a title for the provided user task"
        );
        assert!(title_agent.entry);

        // Verify developer agent
        let dev_agent = workflows
            .agents
            .iter()
            .find(|a| a.id.as_str() == "developer")
            .expect("Developer agent not found");

        assert_eq!(
            dev_agent.description,
            "Does all the engineering tasks provided by the user"
        );
        assert!(dev_agent.entry);
    }
}
