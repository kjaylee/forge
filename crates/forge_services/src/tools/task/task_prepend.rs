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

/// Add a task to the beginning of the task list. This tool prepends a new task
/// to the task list, making it the next item to be processed when using
/// task_next. Use this when you have an urgent or high-priority task that
/// should be handled before existing pending tasks. The task will be created
/// with a pending status and will be the first available for processing.
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
        context
            .send_text(TitleFormat::debug("TaskPrepend").sub_title(&input.description))
            .await?;

        self.infra.task_service().prepend(input.description).await?;

        // Calculate stats manually
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = TaskListResult {
            message: Some("Task added to the beginning of the list.".to_string()),
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
    async fn test_prepend_task() {
        // Create fixture
        let task_prepend = create_task_prepend();

        let input = TaskPrependInput { description: "Urgent task".to_string(), explanation: None };

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
}
