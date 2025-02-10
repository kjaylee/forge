use std::collections::HashMap;

use forge_domain::{
    Agent, AgentBuilder, Environment, ModelId, NamedTool, Prompt, SystemContext, Variables,
    Workflow, WriteVariable,
};
use forge_tool::tools;

#[derive(Clone)]
pub struct ForgeWorkflow {
    pub title_agent: Agent,
    pub developer_agent: Agent,
}

impl ForgeWorkflow {
    pub fn new(env: Environment) -> Self {
        let mut agent = AgentBuilder::default();

        // Set default configurations
        agent
            .model(ModelId::from_env(&env))
            .ephemeral(true)
            .entry(true);

        let mut title_agent = agent.clone();
        let mut developer_agent = agent.clone();

        title_agent
            .description("Generates a title for the provided user task")
            .user_prompt(Prompt::<Variables>::new(
                "<technical_content>{{task}}</technical_content>",
            ))
            .system_prompt(Prompt::<SystemContext>::new(include_str!(
                "prompts/title.md"
            )))
            .tools(vec![WriteVariable::tool_name()]);

        developer_agent
            .ephemeral(false)
            .description("Does all the engineering tasks provided by the user")
            .user_prompt(Prompt::<Variables>::new("<task>{{task}}</task>"))
            .system_prompt(Prompt::<SystemContext>::new(include_str!(
                "prompts/coding/system.md"
            )))
            .tools(
                tools(&env)
                    .iter()
                    .map(|t| t.definition.name.clone())
                    .collect::<Vec<_>>(),
            );

        Self {
            title_agent: title_agent.build().unwrap(),
            developer_agent: developer_agent.build().unwrap(),
        }
    }
}

impl From<ForgeWorkflow> for Workflow {
    fn from(value: ForgeWorkflow) -> Self {
        Self {
            agents: vec![value.title_agent, value.developer_agent],
            state: HashMap::new(),
            variables: Variables::default(),
        }
    }
}
