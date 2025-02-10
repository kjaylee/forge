use std::sync::Arc;

use forge_domain::{
    AgentBuilder, AgentId, AgentMessage, ChatResponse, Environment, ModelId, Orchestrator, Prompt,
    Provider, ProviderService, SystemContext, ToolService, Transform, Variables, Workflow,
};

use crate::mpsc_stream::MpscStream;

pub struct AgenticWorkflow {
    workflow: Workflow,
    env: Environment,
    tool: Arc<dyn ToolService>,
    provider: Arc<dyn ProviderService>,
}

impl AgenticWorkflow {
    // TODO: figure out better way to add tools for specific agent.
    pub fn new(
        env: Environment,
        tool: Arc<dyn ToolService>,
        provider: Arc<dyn ProviderService>,
    ) -> Self {
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
            .user_prompt(Prompt::<Variables>::new("{{context}}"))
            .provider(Provider::new("open-ai"))
            .tools(vec![])
            .build()
            .unwrap(); // add tool that helps us to save the learnings.

        let learning_finder_agent = agent
            .clone()
            .id(AgentId::new("learning-finder"))
            .system_prompt(Prompt::<SystemContext>::new(include_str!(
                "./prompts/learning_finder.md"
            ))) // fix the path.
            .user_prompt(Prompt::<Variables>::new("{{user_message}}"))
            .provider(Provider::new("open-ai"))
            .tools(vec![]) // add a tool that helps agent retrive the relevent learnings from db.
            .build()
            .unwrap();

        let coding_agent = agent
            .id(AgentId::new("coding-agent"))
            .system_prompt(Prompt::<SystemContext>::new(include_str!(
                "./prompts/coding/system.md"
            )))
            .user_prompt(Prompt::<Variables>::new("<task>{{task}}</task"))
            .provider(Provider::new("open-ai"))
            .tools(vec![]) // add all relevent tools for coding agent.
            .entry(true)
            .ephemeral(true)
            .transforms(vec![
                Transform::Tap {
                    agent_id: AgentId::new("learning-extractor"),
                    input: "context".into(),
                },
                Transform::User {
                    agent_id: AgentId::new("learning-finder"),
                    input: "user_message".into(),
                    output: "task".into(),
                },
            ])
            .build()
            .unwrap();

        Self {
            workflow: Workflow::default().agents(vec![
                coding_agent,
                learning_extractor_agent,
                learning_finder_agent,
            ]),
            tool,
            provider,
            env,
        }
    }

    pub fn run(&mut self, content: &str) -> MpscStream<AgentMessage<ChatResponse>> {
        let env = self.env.clone();
        let provider = self.provider.clone();
        let tool = self.tool.clone();
        let workflow = self.workflow.clone();
        let content = content.to_string();

        let value = MpscStream::spawn(|tx| async move {
            // fill these values up.
            let context = SystemContext {
                env: Some(env.clone()),
                tool_information: None,
                tool_supported: None,
                custom_instructions: None,
                files: vec![],
            };

            let mut input = Variables::default();
            input.add("task", content);
            Orchestrator::new(provider.clone(), tool.clone(), workflow)
                .system_context(context)
                .sender(Some(tx))
                .execute(&input)
                .await;
        });

        value
    }
}
