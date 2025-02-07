use std::sync::Arc;

use forge_domain::{
    ChatRequest, ChatResponse, ProviderService, ResultStream, ToolService, Workflow,
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
    ) -> impl ChatService {
        Live::new(provider, tool)
    }
}

struct Live {
    provider: Arc<dyn ProviderService>,
    tool: Arc<dyn ToolService>,
}

impl Live {
    fn new(provider: Arc<dyn ProviderService>, tool: Arc<dyn ToolService>) -> Self {
        Self { provider, tool }
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
