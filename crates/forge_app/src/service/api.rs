use std::collections::HashMap;
use std::sync::Arc;

use anyhow::Result;
use futures::StreamExt;
use forge_domain::{
    Agent, AgentId, Arena, ChatRequest, ChatResponse, Config, ConfigRepository, Context,
    Conversation, ConversationHistory, ConversationId, ConversationRepository, Environment, FlowId,
    Model, ModelId, Orchestrator, Prompt, PromptTemplate, Provider, ProviderService, ResultStream,
    Schema, SystemContext, ToolDefinition, ToolService, Variables, Workflow, WorkflowId,
};
use forge_tool::tools;

use super::suggestion::{File, SuggestionService};
use super::ui::UIService;
use super::Service;

#[async_trait::async_trait]
pub trait APIService: Send + Sync {
    async fn suggestions(&self) -> Result<Vec<File>>;
    async fn tools(&self) -> Vec<ToolDefinition>;
    async fn context(&self, conversation_id: ConversationId) -> Result<Context>;
    async fn models(&self) -> Result<Vec<Model>>;
    async fn chat(&self, chat: ChatRequest) -> ResultStream<ChatResponse, anyhow::Error>;
    async fn conversations(&self) -> Result<Vec<Conversation>>;
    async fn conversation(&self, conversation_id: ConversationId) -> Result<ConversationHistory>;
    async fn get_config(&self) -> Result<Config>;
    async fn set_config(&self, request: Config) -> Result<Config>;
    async fn environment(&self) -> Result<Environment>;
    async fn init_workflow(&self, id: WorkflowId, input: Variables) -> ResultStream<ChatResponse, anyhow::Error>;
}

impl Service {
    pub fn api_service(env: Environment) -> Result<impl APIService> {
        Live::new(env)
    }
}

#[derive(Clone)]
struct Live {
    provider: Arc<dyn ProviderService>,
    tool: Arc<dyn ToolService>,
    completions: Arc<dyn SuggestionService>,
    ui_service: Arc<dyn UIService>,
    conversation_repo: Arc<dyn ConversationRepository>,
    config_repo: Arc<dyn ConfigRepository>,
    environment: Environment,
    orchestrator: Arc<Orchestrator>,
}

impl Live {
    fn new(env: Environment) -> Result<Self> {
        let provider = Arc::new(Service::provider_service(env.api_key.clone()));
        let tool = Arc::new(Service::tool_service());
        let file_read = Arc::new(Service::file_read_service());

        let system_prompt = Arc::new(Service::system_prompt(
            env.clone(),
            tool.clone(),
            provider.clone(),
            file_read.clone(),
        ));
        // Initialize system context with environment and tool information
        let system_context = SystemContext {
            env: env.clone(),
            tool_information: tool.usage_prompt(),
            tool_supported: true,
            custom_instructions: None,
            files: vec![],
        };

        let schema = Schema::<SystemContext>::new(schemars::schema_for!(SystemContext));

        let system = Prompt {
            template: PromptTemplate::new(include_str!("../prompts/coding/system.md")),
            variables: schema,
        };

        let user_prompt = Prompt {
            template: PromptTemplate::new(include_str!("../prompts/coding/user_task.md")),
            variables: Schema::<Variables>::new(schemars::schema_for!(Variables)),
        };

        let main_agent = Agent {
            id: AgentId::new("main-agent".to_string()),
            provider: Provider::try_new("https://openrouter.ai")?,
            model: ModelId::new(env.large_model_id.clone().as_str()),
            description: "Main agent".to_string(),
            system_prompt: system,
            user_prompt,
            tools: tools().iter().map(|t| t.definition.name.clone()).collect(),
            transforms: vec![],
        };

        let mut handovers = HashMap::new();
        handovers.insert(
            FlowId::Agent(AgentId::new("main-agent".to_string())),
            vec![],
        );
        let workflow = Workflow {
            id: WorkflowId::new("main-workflow"),
            description: "Main workflow".to_string(),
            handovers,
        };

        let arena = Arena {
            agents: vec![main_agent],
            workflows: vec![workflow],
            tools: vec![],
        };

        let orchestrator = Arc::new(Orchestrator::new(
            provider.clone(),
            tool.clone(),
            arena,
            system_context,
        ));

        let user_prompt = Arc::new(Service::user_prompt_service());

        // Create an owned String that will live for 'static
        let sqlite = Arc::new(Service::db_pool_service(env.db_path()));

        let conversation_repo = Arc::new(Service::conversation_repo(sqlite.clone()));
        let config_repo = Arc::new(Service::config_repo(sqlite.clone()));

        let chat_service = Arc::new(Service::chat_service(
            provider.clone(),
            system_prompt.clone(),
            tool.clone(),
            user_prompt,
        ));

        // Use the environment's cwd for completions since that's always available
        let completions = Arc::new(Service::completion_service(env.cwd.clone()));

        let title_service = Arc::new(Service::title_service(provider.clone()));

        let chat_service = Arc::new(Service::ui_service(
            conversation_repo.clone(),
            chat_service,
            title_service,
        ));

        Ok(Self {
            provider,
            tool,
            completions,
            ui_service: chat_service,
            conversation_repo,
            config_repo,
            environment: env,
            orchestrator,
        })
    }
}

#[async_trait::async_trait]
impl APIService for Live {
    async fn suggestions(&self) -> Result<Vec<File>> {
        self.completions.suggestions().await
    }

    async fn tools(&self) -> Vec<ToolDefinition> {
        self.tool.list()
    }

    async fn context(&self, conversation_id: ConversationId) -> Result<Context> {
        Ok(self.conversation_repo.get(conversation_id).await?.context)
    }

    async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.provider.models().await?)
    }

    async fn chat(&self, chat: ChatRequest) -> ResultStream<ChatResponse, anyhow::Error> {
        Ok(self.ui_service.chat(chat).await?)
    }

    async fn conversations(&self) -> Result<Vec<Conversation>> {
        self.conversation_repo.list().await
    }

    async fn conversation(&self, conversation_id: ConversationId) -> Result<ConversationHistory> {
        Ok(self
            .conversation_repo
            .get(conversation_id)
            .await?
            .context
            .into())
    }

    async fn get_config(&self) -> Result<Config> {
        Ok(self.config_repo.get().await?)
    }

    async fn set_config(&self, config: Config) -> Result<Config> {
        self.config_repo.set(config).await
    }

    async fn environment(&self) -> Result<Environment> {
        Ok(self.environment.clone())
    }

    async fn init_workflow(&self, id: WorkflowId, input: Variables) -> ResultStream<ChatResponse, anyhow::Error> {
        let flow_id = FlowId::Workflow(id);
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
        
        // Get the orchestrator from Arc and create a new instance with the response channel
        let orchestrator = {
            let orch = (*self.orchestrator).clone();
            orch.with_response_channel(tx.clone())
        };
        
        // Spawn the execution task
        tokio::spawn(async move {
            if let Err(e) = orchestrator.execute(&flow_id, &input).await {
                let _ = tx.send(Err(e));
            }
            let _ = tx.send(Ok(ChatResponse::Complete));
        });
        
        // Return the receiver as a stream, mapping each value to Result<ChatResponse, anyhow::Error>
        Ok(Box::pin(tokio_stream::wrappers::UnboundedReceiverStream::new(rx)
            ))
    }
}
