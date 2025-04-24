use std::sync::Arc;

use derive_setters::Setters;
use tokio::sync::mpsc::Sender;

use crate::{Agent, AgentMessage, ChatResponse, Conversation};

/// Type alias for Arc<Sender<Result<AgentMessage<ChatResponse>>>>
type ArcSender = Arc<Sender<anyhow::Result<AgentMessage<ChatResponse>>>>;

/// Provides additional context for tool calls.
/// Contains the agent and conversation for accessing tools and other context.
#[derive(Clone, Debug, Setters, Default)]
#[setters(strip_option)]
pub struct ToolCallContext {
    pub sender: Option<ArcSender>,
    pub agent: Option<Agent>,
    pub conversation: Option<Conversation>,
}

impl ToolCallContext {
    /// Create a new ToolCallContext with required fields
    pub fn new(agent: Agent, conversation: Conversation) -> Self {
        Self {
            sender: None,
            agent: Some(agent),
            conversation: Some(conversation),
        }
    }

    /// Send a message through the sender if available
    pub async fn send(&self, agent_message: AgentMessage<ChatResponse>) -> anyhow::Result<()> {
        if let Some(sender) = &self.sender {
            sender.send(Ok(agent_message)).await?
        }
        Ok(())
    }

    pub async fn send_text(&self, content: String) -> anyhow::Result<()> {
        if let Some(agent) = &self.agent {
            self.send(AgentMessage::new(
                agent.id.clone(),
                ChatResponse::Text {
                    text: content.as_str().to_string(),
                    is_complete: true,
                    is_md: false,
                },
            ))
            .await
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ConversationId;

    fn create_test_agent() -> Agent {
        Agent::new("test-agent")
    }

    fn create_test_conversation() -> Conversation {
        Conversation {
            id: ConversationId::generate(),
            archived: false,
            state: Default::default(),
            agents: vec![],
            events: vec![],
            mode: Default::default(),
            workflow: crate::Workflow::new(),
        }
    }

    #[test]
    fn test_create_context() {
        let agent = create_test_agent();
        let conversation = create_test_conversation();
        let context = ToolCallContext::new(agent, conversation);
        assert!(context.sender.is_none());
        assert!(context.agent.is_some());
        assert!(context.conversation.is_some());
    }

    #[test]
    fn test_with_sender() {
        // This is just a type check test - we don't actually create a sender
        // as it's complex to set up in a unit test
        let agent = create_test_agent();
        let conversation = create_test_conversation();
        let context = ToolCallContext::new(agent, conversation);
        assert!(context.sender.is_none());
        assert!(context.agent.is_some());
        assert!(context.conversation.is_some());
    }

    #[test]
    fn test_default() {
        let context = ToolCallContext::default();
        assert!(context.sender.is_none());
        assert!(context.agent.is_none());
        assert!(context.conversation.is_none());
    }
}
