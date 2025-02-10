mod api;

pub use api::*;
use forge_domain::*;
use forge_stream::MpscStream;

#[async_trait::async_trait]
pub trait ForgeAPI {
    async fn suggestions(&self) -> anyhow::Result<Vec<File>>;
    async fn tools(&self) -> Vec<ToolDefinition>;
    async fn context(&self, conversation_id: ConversationId) -> anyhow::Result<Context>;
    async fn models(&self) -> anyhow::Result<Vec<Model>>;
    async fn chat(
        &self,
        chat: ChatRequest,
    ) -> anyhow::Result<MpscStream<anyhow::Result<AgentMessage<ChatResponse>, anyhow::Error>>>;
    async fn conversations(&self) -> anyhow::Result<Vec<Conversation>>;
    async fn conversation(
        &self,
        conversation_id: ConversationId,
    ) -> anyhow::Result<ConversationHistory>;
    async fn get_config(&self) -> anyhow::Result<Config>;
    async fn set_config(&self, request: Config) -> anyhow::Result<Config>;
    async fn environment(&self) -> anyhow::Result<Environment>;
}
