use std::sync::Arc;

use forge_domain::{
    ChatRequest, ChatResponse, Config, Context, Conversation, ConversationId, Environment, Model,
    ResultStream, Tool, ToolDefinition, ToolService,
};
use forge_provider::ProviderService;

use super::chat_service::ConversationHistory;
use super::completion_service::CompletionService;
use super::system_prompt_builder::SystemPrompt;
use super::{ConfigService, ConversationService, File, Service, UIService};
use crate::tools::AgentTool;
use crate::{Error, Result};

#[async_trait::async_trait]
pub trait RootAPIService: Send + Sync {
    async fn completions(&self) -> Result<Vec<File>>;
    async fn tools(&self) -> Vec<ToolDefinition>;
    async fn context(&self, conversation_id: ConversationId) -> Result<Context>;
    async fn models(&self) -> Result<Vec<Model>>;
    async fn chat(&self, chat: ChatRequest) -> ResultStream<ChatResponse, Error>;
    async fn conversations(&self) -> Result<Vec<Conversation>>;
    async fn conversation(&self, conversation_id: ConversationId) -> Result<ConversationHistory>;
    async fn get_config(&self) -> Result<Config>;
    async fn set_config(&self, request: Config) -> Result<Config>;
}

impl Service {
    pub fn root_api_service(env: Environment) -> impl RootAPIService {
        Live::new(env)
    }
}

#[derive(Clone)]
struct Live {
    provider: Arc<dyn ProviderService>,
    tool: Arc<dyn ToolService>,
    completions: Arc<dyn CompletionService>,
    ui_service: Arc<dyn UIService>,
    storage: Arc<dyn ConversationService>,
    config_storage: Arc<dyn ConfigService>,
}

impl Live {
    fn new(env: Environment) -> Self {
        let cwd: String = env.cwd.clone();
        let provider = Arc::new(forge_provider::Service::open_router(env.api_key.clone()));
        let tool = Arc::new(forge_tool::Service::tool_service());
        let file_read = Arc::new(Service::file_read_service());
        let user_prompt = Arc::new(Service::user_prompt_service(file_read.clone()));
        let storage =
            Arc::new(Service::storage_service(&cwd).expect("Failed to create storage service"));
        let completions = Arc::new(Service::completion_service(cwd.clone()));
        let title_service = Arc::new(Service::title_service(provider.clone()));
        let config_storage = Arc::new(
            Service::config_service(&cwd).expect("Failed to create config storage service"),
        );

        // Coding Agent
        let coding_system_prompt = Arc::new(
            SystemPrompt::new(env.clone(), tool.clone(), provider.clone())
                .template(include_str!("../prompts/coding/system.md"))
                .build(),
        );
        let coder = Arc::new(Service::chat_service(
            provider.clone(),
            coding_system_prompt.clone(),
            tool.clone(),
            user_prompt.clone(),
        ));

        // Planning Agent
        let planner_system_prompt = Arc::new(
            SystemPrompt::new(env.clone(), tool.clone(), provider.clone())
                .template(include_str!("../prompts/coding/planner.md"))
                .build(),
        );
        let planner = Arc::new(Service::chat_service(
            provider.clone(),
            planner_system_prompt.clone(),
            tool.clone(),
            user_prompt.clone(),
        ));

        // Researcher Agent
        let researcher_system_prompt = Arc::new(
            SystemPrompt::new(env.clone(), tool.clone(), provider.clone())
                .template(include_str!("../prompts/coding/researcher.md"))
                .build(),
        );
        let researcher = Arc::new(Service::chat_service(
            provider.clone(),
            researcher_system_prompt.clone(),
            tool.clone(),
            user_prompt.clone(),
        ));

        // Tester Agent
        let tester_system_prompt = Arc::new(
            SystemPrompt::new(env.clone(), tool.clone(), provider.clone())
                .template(include_str!("../prompts/coding/tester.md"))
                .build(),
        );
        let tester = Arc::new(Service::chat_service(
            provider.clone(),
            tester_system_prompt.clone(),
            tool.clone(),
            user_prompt.clone(),
        ));

        // Reviewer Agent
        let reviewer_system_prompt = Arc::new(
            SystemPrompt::new(env.clone(), tool.clone(), provider.clone())
                .template(include_str!("../prompts/coding/reviewer.md"))
                .build(),
        );
        let reviewer = Arc::new(Service::chat_service(
            provider.clone(),
            reviewer_system_prompt.clone(),
            tool.clone(),
            user_prompt.clone(),
        ));

        // List of Tools for Orchestrator
        let tester_tool = AgentTool::new(tester, include_str!("../tools/descriptions/tester.md"));
        let reviewer_tool =
            AgentTool::new(reviewer, include_str!("../tools/descriptions/reviewer.md"));
        let researcher_tool = AgentTool::new(
            researcher,
            include_str!("../tools/descriptions/researcher.md"),
        );
        let planner_tool =
            AgentTool::new(planner, include_str!("../tools/descriptions/planner.md"));
        let coder_tool = AgentTool::new(coder, include_str!("../tools/descriptions/coder.md"));

        let orchestrator_tools = Arc::new(forge_tool::Service::from_tools(vec![
            Tool::new(tester_tool),
            Tool::new(reviewer_tool),
            Tool::new(researcher_tool),
            Tool::new(planner_tool),
            Tool::new(coder_tool),
        ]));

        // Orchestrator Agent
        let orchestrator_system_prompt = Arc::new(
            SystemPrompt::new(env.clone(), tool.clone(), provider.clone())
                .template(include_str!("../prompts/coding/orchestrator.md"))
                .build(),
        );
        let orchestrator = Arc::new(Service::chat_service(
            provider.clone(),
            orchestrator_system_prompt.clone(),
            orchestrator_tools.clone(),
            user_prompt.clone(),
        ));

        let chat_service = Arc::new(Service::ui_service(
            storage.clone(),
            orchestrator.clone(),
            title_service,
        ));

        Self {
            provider,
            tool,
            completions,
            ui_service: chat_service,
            storage,
            config_storage,
        }
    }
}

#[async_trait::async_trait]
impl RootAPIService for Live {
    async fn completions(&self) -> Result<Vec<File>> {
        self.completions.list().await
    }

    async fn tools(&self) -> Vec<ToolDefinition> {
        self.tool.list()
    }

    async fn context(&self, conversation_id: ConversationId) -> Result<Context> {
        Ok(self
            .storage
            .get_conversation(conversation_id)
            .await?
            .context)
    }

    async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.provider.models().await?)
    }

    async fn chat(&self, chat: ChatRequest) -> ResultStream<ChatResponse, Error> {
        Ok(self.ui_service.chat(chat).await?)
    }

    async fn conversations(&self) -> Result<Vec<Conversation>> {
        self.storage.list_conversations().await
    }

    async fn conversation(&self, conversation_id: ConversationId) -> Result<ConversationHistory> {
        Ok(self
            .storage
            .get_conversation(conversation_id)
            .await?
            .context
            .into())
    }

    async fn get_config(&self) -> Result<Config> {
        Ok(self.config_storage.get().await?)
    }

    async fn set_config(&self, request: Config) -> Result<Config> {
        self.config_storage.set(request).await
    }
}
