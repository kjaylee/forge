use std::sync::Arc;

use forge_domain::{
    ConversationId, Learning, LearningRepository, ToolCallService, ToolDescription,
};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

/// A tool that captures and stores important information learned during conversations.
/// This includes user preferences, project requirements, technical constraints,
/// and other contextual information that can be used to improve future interactions.
#[derive(ToolDescription)]
pub struct LearningTool {
    conversation_id: ConversationId,
    learning_repository: Arc<dyn LearningRepository + Send + Sync>,
}

#[derive(Deserialize, JsonSchema)]
/// Each learning represents a piece of information that was discovered or
/// clarified during the conversation, such as:
/// - User's coding style preferences
/// - Project-specific requirements or constraints
/// - Technical decisions and their rationale
/// - Important context about the codebase
pub struct LearningInput {
    /// List of learnings to store. Each string should be a clear and concise
    /// statement capturing a single piece of information learned during the
    /// conversation.
    pub learnings: Vec<String>,
}

#[async_trait::async_trait]
impl ToolCallService for LearningTool {
    type Input = LearningInput;
    type Output = String;
    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let _ = self
            .learning_repository
            .save(Learning::new(self.conversation_id.clone(), input.learnings))
            .await
            .map_err(|e| e.to_string())?;
        Ok("Learnings stored successfully".to_string())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use anyhow::Result;
    use forge_domain::ConversationId;

    use super::*;

    struct TestLearningRepository {
        learnings: Arc<Mutex<Vec<Learning>>>,
    }

    impl TestLearningRepository {
        fn new() -> Self {
            Self {
                learnings: Arc::new(Mutex::new(Vec::new())),
            }
        }
    }

    #[async_trait::async_trait]
    impl LearningRepository for TestLearningRepository {
        async fn list_learnings(&self) -> Result<Vec<Learning>> {
            Ok(self.learnings.lock().unwrap().clone())
        }

        async fn get_recent_learnings(&self, n: usize) -> Result<Vec<Learning>> {
            let learnings = self.learnings.lock().unwrap();
            Ok(learnings.iter().rev().take(n).cloned().collect())
        }

        async fn save(&self, learning: Learning) -> Result<()> {
            self.learnings.lock().unwrap().push(learning);
            Ok(())
        }
    }

    #[tokio::test]
    async fn test_save_learnings() {
        let repo = Arc::new(TestLearningRepository::new());
        let conversation_id = ConversationId::generate();
        let tool = LearningTool {
            conversation_id: conversation_id.clone(),
            learning_repository: repo.clone(),
        };

        let input = LearningInput {
            learnings: vec!["learning1".to_string(), "learning2".to_string()],
        };

        // Save learnings
        let result = tool.call(input).await.unwrap();
        assert_eq!(result, "Learnings stored successfully");

        // Verify learnings were saved
        let saved_learnings = repo.list_learnings().await.unwrap();
        assert_eq!(saved_learnings.len(), 1);
        assert_eq!(saved_learnings[0].conversation_id, conversation_id);
        assert_eq!(saved_learnings[0].learnings, vec!["learning1", "learning2"]);
    }

    #[tokio::test]
    async fn test_get_recent_learnings() {
        let repo = Arc::new(TestLearningRepository::new());
        let conversation_id = ConversationId::generate();
        let tool = LearningTool {
            conversation_id: conversation_id.clone(),
            learning_repository: repo.clone(),
        };

        // Save multiple learnings
        for i in 0..5 {
            let input = LearningInput {
                learnings: vec![format!("learning{}", i)],
            };
            tool.call(input).await.unwrap();
        }

        // Get recent learnings
        let recent = repo.get_recent_learnings(3).await.unwrap();
        assert_eq!(recent.len(), 3);
        assert_eq!(recent[0].learnings, vec!["learning4"]);
        assert_eq!(recent[1].learnings, vec!["learning3"]);
        assert_eq!(recent[2].learnings, vec!["learning2"]);
    }
}
