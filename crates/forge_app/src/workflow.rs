use forge_domain::{
    Agent, AgentBuilder, AgentId, Environment, ModelId, Prompt, Provider, SystemContext, Variables,
};

struct Workflow {
    learning_extractor_agent: Agent,
    learning_finder_agent: Agent,
}

impl Workflow {
    pub fn new(env: Environment) -> Self {
        let mut agent = AgentBuilder::default();
        agent
            .entry(false)
            .ephemeral(false)
            .handovers(vec![])
            .transforms(vec![])
            .model(ModelId::from_env(&env));

        let learning_extractor_agent = agent
            .clone()
            .id(AgentId::new("learning-extractor"))
            .system_prompt(Prompt::<SystemContext>::new(include_str!(
                "./prompts/learning_extractor.md"
            ))) // fix the path.
            .user_prompt(Prompt::<Variables>::new("{{task}}"))
            .provider(Provider::new("open-ai"))
            .tools(vec![])
            .build()
            .unwrap(); // add tool that helps us to save the learnings.

        let learning_finder_agent = agent
            .id(AgentId::new("learning-finder"))
            .system_prompt(Prompt::<SystemContext>::new(include_str!(
                "./prompts/learning_finder.md"
            ))) // fix the path.
            .user_prompt(Prompt::<Variables>::new("{{task}}"))
            .provider(Provider::new("open-ai"))
            .tools(vec![])
            .build()
            .unwrap();

        Self { learning_extractor_agent, learning_finder_agent }
    }
}
