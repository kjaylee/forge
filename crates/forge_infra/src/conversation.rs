use forge_domain::{
    AgentId, Context, Conversation, ConversationId, ConversationRepository, Workflow,
};

pub struct ForgeWorkflowRepository {}

impl Default for ForgeWorkflowRepository {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeWorkflowRepository {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl ConversationRepository for ForgeWorkflowRepository {
    async fn get(&self, id: &ConversationId) -> anyhow::Result<Option<Conversation>> {
        todo!()
    }
    async fn create(&self, workflow: Workflow) -> anyhow::Result<ConversationId> {
        todo!()
    }
    async fn complete_turn(&self, id: &ConversationId, agent: &AgentId) -> anyhow::Result<()> {
        todo!()
    }
    async fn set_context(
        &self,
        id: &ConversationId,
        agent: &AgentId,
        context: Context,
    ) -> anyhow::Result<()> {
        todo!()
    }
}
