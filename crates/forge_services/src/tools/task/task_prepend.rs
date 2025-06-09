use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_display::TitleFormat;
use forge_domain::{
    ExecutableTool, NamedTool, TaskPrependInput, ToolCallContext, ToolDescription, ToolName,
    ToolOutput,
};
use forge_tool_macros::ToolDescription;

use crate::task::TaskListResult;
use crate::Infrastructure;

/// Add multiple tasks to the beginning of the task list. This tool prepends a
/// list of tasks to the task list, making them the next items to be processed
/// when using task_next. Use this when you have urgent or high-priority tasks
/// that should be handled before existing pending tasks. The tasks will be
/// created with a pending status and will be the first available for
/// processing.
///
/// Provide a list of task descriptions in the 'descriptions' field. The list
/// cannot be empty.
#[derive(Debug, ToolDescription)]
pub struct TaskPrepend<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskPrepend<F> {
    /// Creates a new TaskPrepend tool with the given infrastructure.
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F> NamedTool for TaskPrepend<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_task_prepend")
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for TaskPrepend<F> {
    type Input = TaskPrependInput;

    async fn call(&self, context: &mut ToolCallContext, input: Self::Input) -> Result<ToolOutput> {
        // Validate input
        if input.descriptions.is_empty() {
            return Err(anyhow::anyhow!("descriptions list cannot be empty"));
        }

        // Handle bulk operation
        let descriptions = &input.descriptions;
        context
            .send_text(
                TitleFormat::debug("TaskPrepend")
                    .sub_title(format!("Adding {} tasks", descriptions.len())),
            )
            .await?;

        self.infra
            .task_service()
            .prepend_bulk(descriptions.clone())
            .await?;

        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = TaskListResult {
            message: Some(format!(
                "{} tasks added to the beginning of the list.",
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

    fn create_task_prepend() -> TaskPrepend<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskPrepend::new(infra)
    }

    #[tokio::test]
    async fn test_prepend_single_task() {
        // Create fixture
        let task_prepend = create_task_prepend();

        let input = TaskPrependInput {
            descriptions: vec!["Urgent task".to_string()],
            explanation: None,
        };

        // Execute the fixture
        let result = task_prepend
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_prepend_bulk_tasks() {
        // Create fixture
        let task_prepend = create_task_prepend();

        let input = TaskPrependInput {
            descriptions: vec![
                "First urgent task".to_string(),
                "Second urgent task".to_string(),
                "Third urgent task".to_string(),
            ],
            explanation: None,
        };

        // Execute the fixture
        let result = task_prepend
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_prepend_empty_list_fails() {
        // Create fixture
        let task_prepend = create_task_prepend();

        let input = TaskPrependInput { descriptions: vec![], explanation: None };

        // Execute the fixture
        let result = task_prepend
            .call(&mut ToolCallContext::default(), input)
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("descriptions list cannot be empty"));
    }
}
