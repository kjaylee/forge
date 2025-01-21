use std::sync::Arc;

use forge_domain::EmbeddingsRepository;
use forge_domain::{NamedTool, ToolCallService, ToolDescription};

use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

/// When new information is discovered, use this tool to store
/// and preserve it for future conversations. Each stored learning captures
/// a piece of information that emerged during the conversation, including:
/// - User's coding style preferences
/// - Project-specific requirements or constraints
/// - Technical decisions and their rationale
/// - Important context about the codebase
#[derive(ToolDescription)]
pub struct Learning {
    learning_repository: Arc<dyn EmbeddingsRepository>,
}

impl NamedTool for Learning {
    fn tool_name(&self) -> forge_domain::ToolName {
        forge_domain::ToolName::new("tool_forge_code_learning")
    }
}

impl Learning {
    pub fn new(learning_repository: Arc<dyn EmbeddingsRepository>) -> Self {
        Self { learning_repository }
    }
}

#[derive(Deserialize, JsonSchema)]
pub struct LearningInput {
    /// List of learnings to store. Each string should be a clear and concise
    /// statement capturing a single piece of information learned during the
    /// conversation.
    pub learnings: Vec<String>,
}

#[async_trait::async_trait]
impl ToolCallService for Learning {
    type Input = LearningInput;
    async fn call(&self, input: Self::Input) -> Result<String, String> {
        if input.learnings.is_empty() {
            return Err("No learnings provided".to_string());
        }

        for learning in input.learnings {
            let _ = self
                .learning_repository
                .insert(learning, vec!["learning".to_owned()])
                .await
                .map_err(|e| e.to_string())?;
        }

        Ok("Learnings stored successfully".to_string())
    }
}

#[cfg(test)]
pub mod tests {
    use std::sync::Mutex;

    use super::*;
    use forge_domain::{Embedding, Information};
    use uuid::Uuid;

    // A simple mock implementation of EmbeddingsRepository for testing
    #[derive(Default)]
    pub struct MockEmbeddingsRepository {
        insertion_count: Mutex<u8>,
    }

    #[async_trait::async_trait]
    impl EmbeddingsRepository for MockEmbeddingsRepository {
        async fn get(&self, _: Uuid) -> anyhow::Result<Option<Information>> {
            todo!()
        }

        async fn insert(&self, _: String, _: Vec<String>) -> anyhow::Result<Embedding> {
            *self.insertion_count.lock().unwrap() += 1;
            Ok(Embedding::new(vec![]))
        }

        async fn search(
            &self,
            _: Embedding,
            _: Vec<String>,
            _: usize,
        ) -> anyhow::Result<Vec<Information>> {
            todo!()
        }
    }

    #[tokio::test]
    async fn test_empty_learnings() {
        let learning_repository = Arc::new(MockEmbeddingsRepository::default());
        let learning = Learning::new(learning_repository.clone());
        let input = LearningInput { learnings: vec![] };
        let result = learning.call(input).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_tool_call() {
        let learning_repository = Arc::new(MockEmbeddingsRepository::default());
        let learning = Learning::new(learning_repository.clone());
        let input = LearningInput {
            learnings: vec!["Test learning".to_string(), "Test Learning -2".to_string()],
        };
        let result = learning.call(input).await;
        assert!(result.is_ok());
        assert!(*learning_repository.insertion_count.lock().unwrap() == 2);
    }
}
