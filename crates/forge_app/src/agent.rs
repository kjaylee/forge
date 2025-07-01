use std::sync::Arc;

use forge_domain::{
    Agent, ChatCompletionMessage, Context, Conversation, ModelId, ResultStream, ToolCallContext,
    ToolCallFull, ToolResult,
};

use crate::tool_registry::ToolRegistry;
use crate::{ConversationService, FollowUpService, ProviderService, Services, TemplateService};

/// Agent service trait that provides core chat and tool call functionality.
/// This trait abstracts the essential operations needed by the Orchestrator.
#[async_trait::async_trait]
pub trait AgentService: Send + Sync + 'static {
    /// Execute a chat completion request
    async fn chat_agent(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error>;

    /// Execute a tool call
    async fn call(
        &self,
        agent: &Agent,
        context: &mut ToolCallContext,
        call: ToolCallFull,
    ) -> ToolResult;

    /// Render a template with the provided object
    async fn render(
        &self,
        template: &str,
        object: &(impl serde::Serialize + Sync),
    ) -> anyhow::Result<String>;

    /// Synchronize the on-going conversation
    async fn update(&self, conversation: Conversation) -> anyhow::Result<()>;

    /// Present a single selection prompt to the user
    async fn select_one(
        &self,
        message: &str,
        options: Vec<String>,
    ) -> anyhow::Result<Option<String>>;
}

/// Blanket implementation of AgentService for any type that implements Services
#[async_trait::async_trait]
impl<T: Services> AgentService for T {
    async fn chat_agent(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        self.chat(id, context).await
    }

    async fn call(
        &self,
        agent: &Agent,
        context: &mut ToolCallContext,
        call: ToolCallFull,
    ) -> ToolResult {
        let registry = ToolRegistry::new(Arc::new(self.clone()));
        registry.call(agent, context, call).await
    }

    async fn render(
        &self,
        template: &str,
        object: &(impl serde::Serialize + Sync),
    ) -> anyhow::Result<String> {
        self.render_template(template, object).await
    }

    async fn update(&self, conversation: Conversation) -> anyhow::Result<()> {
        self.upsert(conversation).await
    }

    async fn select_one(
        &self,
        message: &str,
        options: Vec<String>,
    ) -> anyhow::Result<Option<String>> {
        let response = self
            .follow_up_service()
            .follow_up(message.to_string(), options, Some(false))
            .await?;

        // Parse the response to extract just the selected option
        if let Some(response) = response {
            if let Some(selected) = response.strip_prefix("User selected: ") {
                Ok(Some(selected.to_string()))
            } else {
                Ok(Some(response))
            }
        } else {
            Ok(None)
        }
    }
}
