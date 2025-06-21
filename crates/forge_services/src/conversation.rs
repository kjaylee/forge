use std::collections::HashMap;
use std::sync::Arc;

use anyhow::{Context as AnyhowContext, Result};
use forge_app::{ConversationService, McpService};
use forge_domain::{Conversation, ConversationId, TaskList, Workflow};
use tokio::sync::Mutex;

/// Service for managing conversations, including creation, retrieval, and
/// updates
#[derive(Clone)]
pub struct ForgeConversationService<M> {
    workflows: Arc<Mutex<HashMap<ConversationId, Conversation>>>,
    mcp_service: Arc<M>,
}

impl<M: McpService> ForgeConversationService<M> {
    /// Creates a new ForgeConversationService with the provided MCP service
    pub fn new(mcp_service: Arc<M>) -> Self {
        Self { workflows: Arc::new(Mutex::new(HashMap::new())), mcp_service }
    }
}

#[async_trait::async_trait]
impl<M: McpService> ConversationService for ForgeConversationService<M> {
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

    async fn create_conversation(&self, workflow: Workflow) -> Result<Conversation> {
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

    async fn task_list(&self, conversation_id: &ConversationId) -> Result<TaskList> {
        let workflows = self.workflows.lock().await;
        workflows
            .get(conversation_id)
            .map(|c| c.task_list.clone())
            .context("Conversation not found")
    }

    async fn set_task_list(&self, conversation_id: &ConversationId, task_list: TaskList) -> Result<()> {
        let mut workflows = self.workflows.lock().await;
        if let Some(conversation) = workflows.get_mut(conversation_id) {
            conversation.task_list = task_list;
            Ok(())
        } else {
            Err(anyhow::anyhow!("Conversation not found"))
        }
    }
}
