use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_display::TitleFormat;
use forge_domain::{
    ExecutableTool, NamedTool, TaskNextInput, ToolCallContext, ToolDescription, ToolName,
    ToolOutput,
};
use forge_tool_macros::ToolDescription;

use crate::task::TaskListResult;
use crate::Infrastructure;

/// Get the next pending task from the task list. This tool marks the first
/// pending task as In Progress and returns it for processing. Use this when
/// you're ready to start working on the next available task. The task status
/// will be updated from Pending to InProgress, making it clear that work has
/// begun on this item. Returns empty result if no pending tasks are available.
#[derive(Debug, ToolDescription)]
pub struct TaskNext<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskNext<F> {
    /// Creates a new TaskNext tool with the given infrastructure.
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F> NamedTool for TaskNext<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_task_next")
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for TaskNext<F> {
    type Input = TaskNextInput;

    async fn call(&self, context: &mut ToolCallContext, _input: Self::Input) -> Result<ToolOutput> {
        context.send_text(TitleFormat::debug("TaskNext")).await?;

        let task_option = self.infra.task_service().pop_front().await?;

        // Calculate stats manually
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = if let Some(task) = task_option {
            TaskListResult { message: None, next_task: Some(task), stats, tasks: None }
        } else {
            TaskListResult {
                message: Some("No pending tasks found.".to_string()),
                next_task: None,
                stats,
                tasks: None,
            }
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

    fn create_task_next() -> TaskNext<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskNext::new(infra)
    }

    #[tokio::test]
    async fn test_next_task() {
        // Create fixture
        let task_next = create_task_next();

        let input = TaskNextInput { explanation: None };

        // Execute the fixture
        let result = task_next
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }
}
