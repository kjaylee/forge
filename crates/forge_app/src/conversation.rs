use std::sync::Arc;
use std::{collections::HashMap, sync::Mutex};

use anyhow::{Context as AnyhowContext, Result};
use forge_domain::{AgentId, Context, Conversation, ConversationId, ConversationService, Workflow};
use serde_json::Value;

#[derive(Clone)]
pub struct ForgeConversationService {
    workflows: Arc<Mutex<HashMap<ConversationId, Conversation>>>,
}

impl Default for ForgeConversationService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeConversationService {
    pub fn new() -> Self {
        Self { workflows: Arc::new(Mutex::new(HashMap::new())) }
    }
}

#[async_trait::async_trait]
impl ConversationService for ForgeConversationService {
    fn update<F, T>(&self, id: &ConversationId, f: F) -> Result<T>
    where
        F: FnOnce(&mut Conversation) -> T + Send,
    {
        let mut workflows = self.workflows.lock().unwrap();
        let conversation = workflows.get_mut(id).context("Conversation not found")?;
        Ok(f(conversation))
    }

    async fn get(&self, id: &ConversationId) -> Result<Option<Conversation>> {
        Ok(self.workflows.lock().unwrap().get(id).cloned())
    }

    async fn create(&self, workflow: Workflow) -> Result<ConversationId> {
        let id = ConversationId::generate();
        let conversation = Conversation::new(id.clone(), workflow);
        self.workflows
            .lock()
            .unwrap()
            .insert(id.clone(), conversation);
        Ok(id)
    }

    async fn inc_turn(&self, id: &ConversationId, agent: &AgentId) -> Result<()> {
        self.update(id, |c| {
            c.state.entry(agent.clone()).or_default().turn_count += 1;
        })
    }

    async fn set_context(
        &self,
        id: &ConversationId,
        agent: &AgentId,
        context: Context,
    ) -> Result<()> {
        self.update(id, |c| {
            c.state.entry(agent.clone()).or_default().context = Some(context);
        })
    }

    async fn get_variable(&self, id: &ConversationId, key: &str) -> Result<Option<Value>> {
        self.update(id, |c| c.get_variable(key).cloned())
    }

    async fn set_variable(&self, id: &ConversationId, key: String, value: Value) -> Result<()> {
        self.update(id, |c| {
            c.set_variable(key, value);
        })
    }

    async fn delete_variable(&self, id: &ConversationId, key: &str) -> Result<bool> {
        self.update(id, |c| c.delete_variable(key))
    }
}
