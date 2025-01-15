use std::sync::Arc;

use forge_domain::{
    Learning as LearningModel, LearningRepository, NamedTool, ToolCallService, ToolDescription,
};
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
    learning_repository: Arc<dyn LearningRepository + Send + Sync>,
    current_working_directory: String,
}

impl NamedTool for Learning {
    fn tool_name(&self) -> forge_domain::ToolName {
        forge_domain::ToolName::new("learning")
    }
}

impl Learning {
    pub fn new(
        current_working_directory: String,
        learning_repository: Arc<dyn LearningRepository + Send + Sync>,
    ) -> Self {
        Self { current_working_directory, learning_repository }
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
    type Output = String;
    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        if input.learnings.is_empty() {
            return Err("No learnings provided".to_string());
        }

        let _ = self
            .learning_repository
            .save(LearningModel::new(
                self.current_working_directory.clone(),
                input.learnings,
            ))
            .await
            .map_err(|e| e.to_string())?;
        Ok("Learnings stored successfully".to_string())
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;
    use std::sync::Mutex;

    use anyhow::Result;
    use tempfile::TempDir;

    use super::*;

    pub struct TestLearningRepository {
        learnings: Arc<Mutex<HashMap<String, Vec<LearningModel>>>>,
    }

    impl TestLearningRepository {
        pub fn new() -> Self {
            Self { learnings: Arc::new(Mutex::new(HashMap::default())) }
        }
    }

    #[async_trait::async_trait]
    impl LearningRepository for TestLearningRepository {
        async fn list_learnings(&self) -> Result<Vec<LearningModel>> {
            let values = self
                .learnings
                .lock()
                .unwrap()
                .values()
                .flatten()
                .cloned()
                .collect();
            Ok(values)
        }

        async fn recent_learnings(&self, cwd: &str, n: usize) -> Result<Vec<LearningModel>> {
            let learnings = self.learnings.lock().unwrap();
            let recent_learnings = learnings.get(cwd).map_or(vec![], |learnings| {
                let start_idx = std::cmp::max(0, learnings.len() as isize - n as isize) as usize;
                learnings[start_idx..].to_vec()
            });
            Ok(recent_learnings)
        }

        async fn save(&self, learning: LearningModel) -> Result<()> {
            self.learnings
                .lock()
                .unwrap()
                .entry(learning.current_working_directory.clone())
                .or_default()
                .push(learning);
            Ok(())
        }
    }

    fn test_cwd() -> TempDir {
        TempDir::new().unwrap()
    }

    #[tokio::test]
    async fn test_save_learnings() {
        let repo = Arc::new(TestLearningRepository::new());
        let current_working_directory = test_cwd().path().to_string_lossy().to_string();
        let tool = Learning::new(current_working_directory.clone(), repo.clone());

        let input = LearningInput {
            learnings: vec!["learning1".to_string(), "learning2".to_string()],
        };

        // Save learnings
        let result = tool.call(input).await.unwrap();
        assert_eq!(result, "Learnings stored successfully");

        // Verify learnings were saved
        let saved_learnings = repo.list_learnings().await.unwrap();
        assert_eq!(saved_learnings.len(), 1);
        assert_eq!(
            saved_learnings[0].current_working_directory,
            current_working_directory
        );
        assert_eq!(saved_learnings[0].learnings, vec!["learning1", "learning2"]);
    }

    #[tokio::test]
    async fn test_get_recent_learnings() {
        let repo = Arc::new(TestLearningRepository::new());
        let current_working_directory = test_cwd().path().to_string_lossy().to_string();
        let tool = Learning {
            current_working_directory: current_working_directory.clone(),
            learning_repository: repo.clone(),
        };

        // Save multiple learnings
        for i in 0..5 {
            let input = LearningInput { learnings: vec![format!("learning{}", i)] };
            tool.call(input).await.unwrap();
        }

        // Get recent learnings
        let recent = repo
            .recent_learnings(current_working_directory.as_str(), 3)
            .await
            .unwrap();
        assert_eq!(recent.len(), 3);
        assert_eq!(recent[0].learnings, vec!["learning2"]);
        assert_eq!(recent[1].learnings, vec!["learning3"]);
        assert_eq!(recent[2].learnings, vec!["learning4"]);
    }

    #[tokio::test]
    async fn test_raise_error_when_empty_learnings_provided() {
        let repo = Arc::new(TestLearningRepository::new());
        let current_working_directory = test_cwd().path().to_string_lossy().to_string();
        let tool = Learning { current_working_directory, learning_repository: repo.clone() };

        let input = LearningInput { learnings: vec![] };
        let result = tool.call(input).await.unwrap_err();
        assert_eq!(result, "No learnings provided");
    }
}
