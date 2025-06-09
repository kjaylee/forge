use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_display::TitleFormat;
use forge_domain::{
    ExecutableTool, NamedTool, TaskAddInput, ToolCallContext, ToolDescription, ToolName, ToolOutput,
};
use forge_tool_macros::ToolDescription;

use crate::task::TaskListResult;
use crate::Infrastructure;

/// Add multiple tasks to the end of the task list. This tool appends a list of
/// tasks to the task list, making them the last items to be processed. Use this
/// when you want to add multiple tasks that should be handled after existing
/// pending tasks. The tasks will be created with a pending status and will be
/// available for processing via the task_next tool.
///
/// Provide a list of task descriptions in the 'descriptions' field. The list
/// cannot be empty.
#[derive(Debug, ToolDescription)]
pub struct TaskAppend<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskAppend<F> {
    /// Creates a new TaskAdd tool with the given infrastructure.
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F> NamedTool for TaskAppend<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_task_add")
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for TaskAppend<F> {
    type Input = TaskAddInput;

    async fn call(&self, context: &mut ToolCallContext, input: Self::Input) -> Result<ToolOutput> {
        // Validate input
        if input.descriptions.is_empty() {
            return Err(anyhow::anyhow!("descriptions list cannot be empty"));
        }

        // Handle bulk operation
        let descriptions = &input.descriptions;
        context
            .send_text(
                TitleFormat::debug("TaskAdd")
                    .sub_title(format!("Adding {} tasks", descriptions.len())),
            )
            .await?;

        self.infra
            .task_service()
            .append_bulk(descriptions.clone())
            .await?;

        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = TaskListResult {
            message: Some(format!(
                "{} tasks added to the end of the list.",
                descriptions.len()
            )),
            next_task: None,
            stats,
            tasks: None,
        };

        Ok(ToolOutput::text(result.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use forge_domain::ToolCallContext;

    use super::*;
    use crate::attachment::tests::MockInfrastructure;

    fn create_task_add() -> TaskAppend<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskAppend::new(infra)
    }

    #[tokio::test]
    async fn test_add_single_task() {
        // Create fixture
        let task_add = create_task_add();

        let input = TaskAddInput {
            descriptions: vec!["Test task".to_string()],
            explanation: None,
        };

        // Execute the fixture
        let result = task_add
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_add_bulk_tasks() {
        // Create fixture
        let task_add = create_task_add();

        let input = TaskAddInput {
            descriptions: vec![
                "First task".to_string(),
                "Second task".to_string(),
                "Third task".to_string(),
            ],
            explanation: None,
        };

        // Execute the fixture
        let result = task_add
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_add_empty_list_fails() {
        // Create fixture
        let task_add = create_task_add();

        let input = TaskAddInput { descriptions: vec![], explanation: None };

        // Execute the fixture
        let result = task_add.call(&mut ToolCallContext::default(), input).await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("descriptions list cannot be empty"));
    }

    #[tokio::test]
    async fn test_add_multiple_operations() {
        // Create fixture
        let task_add = create_task_add();

        // First add a single task
        let single_input = TaskAddInput {
            descriptions: vec!["Single task".to_string()],
            explanation: None,
        };

        let result1 = task_add
            .call(&mut ToolCallContext::default(), single_input)
            .await
            .unwrap();

        // Then add bulk tasks
        let bulk_input = TaskAddInput {
            descriptions: vec!["Bulk task 1".to_string(), "Bulk task 2".to_string()],
            explanation: None,
        };

        let result2 = task_add
            .call(&mut ToolCallContext::default(), bulk_input)
            .await
            .unwrap();

        // Verify both operations succeeded
        assert!(result1
            .as_str()
            .unwrap()
            .contains("1 tasks added to the end of the list"));
        assert!(result2
            .as_str()
            .unwrap()
            .contains("2 tasks added to the end of the list"));
    }
}
