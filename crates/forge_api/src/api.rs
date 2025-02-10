use std::sync::Arc;

use anyhow::Result;
use forge_app::{ExecutorService, ForgeApp, SuggestionService};
use forge_domain::{
    AgentMessage, ChatRequest, ChatResponse, Config, ConfigRepository, Context, Conversation,
    ConversationHistory, ConversationId, ConversationRepository, Environment, EnvironmentService,
    File, Model, ProviderService, ToolDefinition, ToolService,
};
use forge_stream::MpscStream;

use crate::ForgeAPI;

pub struct API<F> {
    app: Arc<F>,
}

impl<F: ForgeApp> API<F> {
    pub fn new(app: Arc<F>) -> Result<Self> {
        Ok(Self { app })
    }
}

#[async_trait::async_trait]
impl<F: ForgeApp> ForgeAPI for API<F> {
    async fn suggestions(&self) -> Result<Vec<File>> {
        self.app.suggestion_service().suggestions().await
    }

    async fn tools(&self) -> Vec<ToolDefinition> {
        self.app.tool_service().list()
    }

    async fn context(&self, conversation_id: ConversationId) -> Result<Context> {
        Ok(self
            .app
            .conversation_repository()
            .get(conversation_id)
            .await?
            .context)
    }

    async fn models(&self) -> Result<Vec<Model>> {
        Ok(self.app.provider_service().models().await?)
    }

    async fn chat(
        &self,
        chat: ChatRequest,
    ) -> anyhow::Result<MpscStream<Result<AgentMessage<ChatResponse>, anyhow::Error>>> {
        Ok(self.app.executor_service().chat(chat).await?)
    }

    async fn conversations(&self) -> Result<Vec<Conversation>> {
        self.app.conversation_repository().list().await
    }

    async fn conversation(&self, conversation_id: ConversationId) -> Result<ConversationHistory> {
        Ok(self
            .app
            .conversation_repository()
            .get(conversation_id)
            .await?
            .context
            .into())
    }

    async fn get_config(&self) -> Result<Config> {
        Ok(self.app.config_repository().get().await?)
    }

    async fn set_config(&self, config: Config) -> Result<Config> {
        self.app.config_repository().set(config).await
    }

    async fn environment(&self) -> Result<Environment> {
        Ok(self
            .app
            .environment_service()
            .get_environment()
            .await?
            .clone())
    }
}
