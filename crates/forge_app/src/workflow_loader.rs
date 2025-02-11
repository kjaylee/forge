use anyhow::{Context, Result};
use forge_domain::{
    Agent, AgentBuilder, AgentId, Downstream, ModelId, Prompt, SystemContext, ToolName, Transform,
    Variables, Workflow,
};
use serde::Deserialize;
use std::path::{Path, PathBuf};

#[derive(Deserialize)]
enum Resolved {}

#[derive(Deserialize)]
enum UnResolved {}

#[derive(Deserialize)]
struct WorkflowConfig<Status = UnResolved> {
    id: String,
    agents: Vec<AgentConfig<Status>>,
}

impl WorkflowConfig<UnResolved> {
    /// resolves relative paths in workflow config.
    fn resolve(self, config_path: PathBuf) -> Result<WorkflowConfig<Resolved>> {
        let config_path = config_path
            .parent()
            .context(format!(
                "Failed to get parent of config path '{}'",
                config_path.display()
            ))?
            .to_path_buf();

        let agents = self
            .agents
            .into_iter()
            .map(|agent| agent.resolve(&config_path))
            .collect::<Result<Vec<_>>>()?;

        Ok(WorkflowConfig { id: self.id, agents })
    }
}

#[derive(Deserialize)]
struct AgentConfig<Status> {
    id: AgentId,
    entry: Option<bool>,
    ephemeral: Option<bool>,
    model: ModelId,
    description: String,
    user_prompt: String,
    system_prompt: String,
    max_turns: Option<u64>,
    tools: Vec<ToolName>,
    #[serde(default)]
    transforms: Vec<Transform>,
    #[serde(default)]
    handovers: Vec<Downstream>,
    #[serde(skip)]
    _marker: std::marker::PhantomData<Status>,
}

/// Resolves a content string to a string by checking if it is a relative or absolute path.
fn resolve_content(content: &str, base_dir: &Path) -> Result<String> {
    let path = Path::new(content);
    let abs_path = base_dir.join(content);
    if path.exists() {
        std::fs::read_to_string(&path)
            .with_context(|| format!("Failed to read content from {}", path.display()))
    } else if abs_path.exists() {
        std::fs::read_to_string(&abs_path)
            .with_context(|| format!("Failed to read content from {}", abs_path.display()))
    } else {
        Ok(content.to_string())
    }
}

impl AgentConfig<UnResolved> {
    /// resolves relative paths in agent config.
    fn resolve(self, base_dir: &PathBuf) -> Result<AgentConfig<Resolved>> {
        Ok(AgentConfig {
            id: self.id,
            entry: self.entry,
            ephemeral: self.ephemeral,
            model: self.model,
            description: self.description,
            user_prompt: resolve_content(&self.user_prompt, base_dir)?,
            system_prompt: resolve_content(&self.system_prompt, base_dir)?,
            max_turns: self.max_turns,
            tools: self.tools,
            transforms: self.transforms,
            handovers: self.handovers,
            _marker: std::marker::PhantomData::<Resolved>,
        })
    }
}

impl TryFrom<AgentConfig<Resolved>> for Agent {
    type Error = anyhow::Error;

    fn try_from(value: AgentConfig<Resolved>) -> Result<Self, Self::Error> {
        let mut builder = AgentBuilder::default()
            .id(value.id)
            .model(value.model)
            .description(&value.description)
            .user_prompt(Prompt::<Variables>::new(&value.user_prompt))
            .system_prompt(Prompt::<SystemContext>::new(&value.system_prompt))
            .tools(value.tools)
            .transforms(value.transforms)
            .handovers(value.handovers);

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
        let content = std::fs::read_to_string(&path).with_context(|| {
            format!(
                "Failed to read workflow configuration from path '{}'",
                path.as_ref().display()
            )
        })?;

        let config: WorkflowConfig<UnResolved> =
            serde_yaml::from_str(&content).context("Failed to parse workflow configuration")?;
        let config = config.resolve(path.as_ref().to_path_buf())?;

        let agents = config
            .agents
            .into_iter()
            .map(Agent::try_from)
            .collect::<Result<Vec<_>>>()?;

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

        let title_agent = workflows
            .agents
            .iter()
            .find(|a| a.id.as_str() == "title-generator")
            .expect("Title generator agent not found");
        assert!(title_agent.handovers.is_empty());
        assert_eq!(
            title_agent.description,
            "Generates a title for the provided user task"
        );
        assert!(title_agent.entry);

        let dev_agent = workflows
            .agents
            .iter()
            .find(|a| a.id.as_str() == "developer")
            .expect("Developer agent not found");

        assert!(dev_agent.handovers.is_empty());
        assert_eq!(
            dev_agent.description,
            "Does all the engineering tasks provided by the user"
        );
        assert!(dev_agent.entry);
    }

    #[test]
    fn test_load_transform() {
        let workflow_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/transform-workflow.yml");
        let workflows = WorkflowLoader::load(workflow_path).unwrap();

        // Title generator agent
        let title_agent = workflows
            .agents
            .iter()
            .find(|a| a.id.as_str() == "title-generator")
            .expect("Title generator agent not found");
        assert!(title_agent.handovers.is_empty());
        assert!(title_agent.transforms.is_empty());
        assert_eq!(
            title_agent.description,
            "Generates a title for the provided user task"
        );
        assert!(!title_agent.entry);


        // Developer agent
        let dev_agent = workflows
            .agents
            .iter()
            .find(|a| a.id.as_str() == "developer")
            .expect("Developer agent not found");


        assert!(dev_agent.handovers.is_empty());
        assert!(!dev_agent.transforms.is_empty());
        assert_eq!(
            dev_agent.description,
            "Does all the engineering tasks provided by the user"
        );
        assert!(dev_agent.entry);
    }
}
