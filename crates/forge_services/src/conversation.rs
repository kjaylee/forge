use std::collections::HashMap;
use std::sync::Arc;

use anyhow::{Context as AnyhowContext, Result};
use forge_domain::{
    AgentId, CompactionResult, Conversation, ConversationId, ConversationService, McpService, ProviderService, Workflow
};
use tokio::sync::Mutex;

/// Service for managing conversations, including creation, retrieval, and
/// updates
#[derive(Clone)]
pub struct ForgeConversationService<M, P> {
    workflows: Arc<Mutex<HashMap<ConversationId, Conversation>>>,
    mcp_service: Arc<M>,
    provider_service: Arc<P>,
}

impl<M: McpService, P: ProviderService> ForgeConversationService<M, P> {
    /// Creates a new ForgeConversationService with the provided compaction
    /// service
    pub fn new(mcp_service: Arc<M>, provider_service: Arc<P>) -> Self {
        Self {
            workflows: Arc::new(Mutex::new(HashMap::new())),
            mcp_service,
            provider_service,
        }
    }
}

#[async_trait::async_trait]
impl<M: McpService, P: ProviderService> ConversationService for ForgeConversationService<M, P> {
    async fn update<F, T>(&self, id: &ConversationId, f: F) -> Result<T>
    where
        F: FnOnce(&mut Conversation) -> T + Send,
    {
        let mut workflows = self.workflows.lock().await;
        let conversation = workflows.get_mut(id).context("Conversation not found")?;
        Ok(f(conversation))
    }

    async fn find(&self, id: &ConversationId) -> Result<Option<Conversation>> {
        Ok(self.workflows.lock().await.get(id).cloned())
    }

    async fn upsert(&self, conversation: Conversation) -> Result<()> {
        self.workflows
            .lock()
            .await
            .insert(conversation.id.clone(), conversation);
        Ok(())
    }

    async fn create(&self, workflow: Workflow) -> Result<Conversation> {
        let id = ConversationId::generate();
        let conversation = Conversation::new(
            id.clone(),
            workflow,
            self.mcp_service
                .list()
                .await?
                .into_iter()
                .map(|a| a.name)
                .collect(),
        );
        self.workflows
            .lock()
            .await
            .insert(id.clone(), conversation.clone());
        Ok(conversation)
    }

    async fn compact_conversation(&self, id: &ConversationId) -> Result<CompactionResult> {
        // Fetch the conversation
        let mut conversation = self
            .find(id)
            .await?
            .ok_or_else(|| anyhow::anyhow!("Conversation not found"))?;

        // Identify the main agent and extract existing context
        let main_agent_id = AgentId::new(Conversation::MAIN_AGENT_NAME);
        let agent = conversation.get_agent(&main_agent_id)?;
        let context = conversation
            .state
            .get(&main_agent_id)
            .and_then(|s| s.context.clone())
            .unwrap_or_default();

        // Compute original metrics
        let original_tokens = context.estimate_token_count() as usize;
        let original_messages = context.messages.len();

        // Perform compaction
        let new_context = self
            .provider_service
            .compact(context.clone(), agent.compact.as_ref().unwrap())
            .await?;

        // Compute compacted metrics
        let compacted_tokens = new_context.estimate_token_count() as usize;
        let compacted_messages = new_context.messages.len();

        // Persist the updated context
        conversation
            .state
            .entry(main_agent_id.clone())
            .or_default()
            .context = Some(new_context.clone());
        self.upsert(conversation).await?;

        // Return metrics
        Ok(CompactionResult::new(
            original_tokens,
            compacted_tokens,
            original_messages,
            compacted_messages,
        ))
    }
}
