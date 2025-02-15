use std::collections::HashMap;
use std::sync::Arc;

use forge_domain::{
    AgentId, Context, Conversation, ConversationId, ConversationRepository, Workflow,
};
use tokio::sync::Mutex;

pub struct InMemoryWorkflowRepository {
    workflows: Arc<Mutex<HashMap<ConversationId, Conversation>>>,
}

impl Default for InMemoryWorkflowRepository {
    fn default() -> Self {
        Self::new()
    }
}

impl InMemoryWorkflowRepository {
    pub fn new() -> Self {
        Self { workflows: Arc::new(Mutex::new(HashMap::new())) }
    }
}

#[async_trait::async_trait]
impl ConversationRepository for InMemoryWorkflowRepository {
    async fn get(&self, id: &ConversationId) -> anyhow::Result<Option<Conversation>> {
        Ok(self.workflows.lock().await.get(id).cloned())
    }

    async fn create(&self, workflow: Workflow) -> anyhow::Result<ConversationId> {
        let id = ConversationId::generate();
        let conversation = Conversation::new(id.clone(), workflow);
        self.workflows.lock().await.insert(id.clone(), conversation);
        Ok(id)
    }

    async fn complete_turn(&self, id: &ConversationId, agent: &AgentId) -> anyhow::Result<()> {
        if let Some(c) = self.workflows.lock().await.get_mut(id) {
            c.state.entry(agent.clone()).or_default().turn_count += 1;
        }
        Ok(())
    }
    async fn set_context(
        &self,
        id: &ConversationId,
        agent: &AgentId,
        context: Context,
    ) -> anyhow::Result<()> {
        if let Some(c) = self.workflows.lock().await.get_mut(id) {
            c.state.entry(agent.clone()).or_default().context = Some(context);
        }
        Ok(())
    }
}
