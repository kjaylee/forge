use anyhow::{Context, Result};
use forge_domain::{
    Agent, AgentBuilder, AgentId, ModelId, Prompt, SystemContext, ToolName, Variables, Workflow,
};
use serde::Deserialize;
use std::path::{Path, PathBuf};

#[derive(Debug, Deserialize)]
enum Resolved {}

#[derive(Debug, Deserialize)]
enum UnResolved {}

#[derive(Debug, Deserialize)]
struct WorkflowConfig<Status = UnResolved> {
    id: String,
    agents: Vec<AgentConfig<Status>>,
}

impl WorkflowConfig<UnResolved> {
    /// resolves the relative paths defined in the workflow file as per the path of config.
    fn resolve(self, config_path: PathBuf) -> Result<WorkflowConfig<Resolved>> {
        let config_path = config_path
            .parent()
            .context("Failed to get parent of config path")?
            .to_path_buf();
        let agents = self
            .agents
            .into_iter()
            .map(|agent| agent.resolve(&config_path))
            .collect::<Result<Vec<_>>>()?;

        Ok(WorkflowConfig { id: self.id, agents })
    }
}

#[derive(Debug, Deserialize)]
struct AgentConfig<Status> {
    id: String,
    entry: Option<bool>,
    ephemeral: Option<bool>,
    model: ModelId,
    description: String,
    user_prompt: String,
    system_prompt: String,
    max_turns: Option<u64>,
    tools: Vec<ToolName>,
    #[serde(skip)]
    _marker: std::marker::PhantomData<Status>,
}

impl AgentConfig<UnResolved> {
    /// resolves the relative paths defined in the config file as per the path of config.
    fn resolve(mut self, base_dir: &PathBuf) -> Result<AgentConfig<Resolved>> {
        let user_prompt_path = Path::new(&self.user_prompt);
        let user_prompt_abs_path = base_dir.join(&self.user_prompt);
        self.user_prompt = if user_prompt_path.exists() || user_prompt_abs_path.exists() {
            let user_prompt_template = std::fs::read_to_string(user_prompt_abs_path)?;
            user_prompt_template
        } else {
            self.user_prompt
        };

        let system_prompt_path = Path::new(&self.system_prompt);
        let system_prompt_abs_path = base_dir.join(&self.system_prompt);
        self.system_prompt = if system_prompt_path.exists() || system_prompt_abs_path.exists() {
            let system_prompt_template = std::fs::read_to_string(system_prompt_abs_path)?;
            system_prompt_template
        } else {
            self.system_prompt
        };

        Ok(AgentConfig {
            id: self.id,
            entry: self.entry,
            ephemeral: self.ephemeral,
            model: self.model,
            description: self.description,
            user_prompt: self.user_prompt,
            system_prompt: self.system_prompt,
            max_turns: self.max_turns,
            tools: self.tools,
            _marker: std::marker::PhantomData::<Resolved>,
        })
    }
}

impl TryFrom<AgentConfig<Resolved>> for Agent {
    type Error = anyhow::Error;

    fn try_from(value: AgentConfig<Resolved>) -> Result<Self, Self::Error> {
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

    /// Load a workflow from a YAML file
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Workflow> {
        let content = std::fs::read_to_string(&path).context(format!(
            "Failed to read workflow configuration from path '{}'",
            path.as_ref().display()
        ))?;

        let config: WorkflowConfig<UnResolved> =
            serde_yaml::from_str(&content).context("Failed to parse workflow configuration")?;
        let config = config.resolve(path.as_ref().to_path_buf())?;

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
