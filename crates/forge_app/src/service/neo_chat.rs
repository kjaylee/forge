use std::sync::Arc;

use forge_domain::{
    ChatRequest, ChatResponse, ConversationRepository, ProviderService, ResultStream, ToolService,
    Workflow,
};

use super::Service;

#[async_trait::async_trait]
pub trait ChatService: Send + Sync {
    async fn chat(
        &self,
        prompt: ChatRequest,
        workflow: Workflow,
    ) -> ResultStream<ChatResponse, anyhow::Error>;
}

impl Service {
    pub fn chat_service(
        provider: Arc<dyn ProviderService>,
        tool: Arc<dyn ToolService>,
        conversation: Arc<dyn ConversationRepository>,
    ) -> impl ChatService {
        Live::new(provider, tool, conversation)
    }
}

struct Live {
    provider: Arc<dyn ProviderService>,
    tool: Arc<dyn ToolService>,
    conversation: Arc<dyn ConversationRepository>,
}

impl Live {
    fn new(
        provider: Arc<dyn ProviderService>,
        tool: Arc<dyn ToolService>,
        conversation: Arc<dyn ConversationRepository>,
    ) -> Self {
        Self { provider, tool, conversation }
    }
}

#[async_trait::async_trait]
impl ChatService for Live {
    async fn chat(
        &self,
        prompt: ChatRequest,
        workflow: Workflow,
    ) -> ResultStream<ChatResponse, anyhow::Error> {
        todo!()
    }
}
