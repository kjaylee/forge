use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_display::TitleFormat;
use forge_domain::{
    ExecutableTool, NamedTool, TaskListDisplayInput, ToolCallContext, ToolDescription, ToolName,
    ToolOutput,
};
use forge_tool_macros::ToolDescription;

use crate::task::TaskListResult;
use crate::Infrastructure;

/// Display all tasks in the task list with their current status. This tool
/// returns a comprehensive view of all tasks organized by status (Pending, In
/// Progress, Completed) along with summary statistics. Use this to get a
/// complete overview of your task list status and progress. The output includes
/// both markdown-formatted display and structured task data for easy parsing.
#[derive(Debug, ToolDescription)]
pub struct TaskListDisplay<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskListDisplay<F> {
    /// Creates a new TaskListDisplay tool with the given infrastructure.
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F> NamedTool for TaskListDisplay<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_task_list")
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for TaskListDisplay<F> {
    type Input = TaskListDisplayInput;

    async fn call(&self, context: &mut ToolCallContext, _input: Self::Input) -> Result<ToolOutput> {
        context.send_text(TitleFormat::debug("TaskList")).await?;

        let tasks = self.infra.task_service().list().await?;
        let markdown = self.infra.task_service().format_markdown().await?;

        // Calculate stats manually
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = TaskListResult {
            message: Some(markdown),
            next_task: None,
            stats,
            tasks: Some(tasks),
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

    fn create_task_list_display() -> TaskListDisplay<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskListDisplay::new(infra)
    }

    #[tokio::test]
    async fn test_list_tasks() {
        // Create fixture
        let task_list_display = create_task_list_display();

        let input = TaskListDisplayInput { explanation: None };

        // Execute the fixture
        let result = task_list_display
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }
}
