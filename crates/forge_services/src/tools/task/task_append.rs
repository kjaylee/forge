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

/// Add a task to the end of the task list. This tool appends a new task to the
/// task list, making it the last item to be processed. Use this when you want
/// to add tasks that should be handled after existing pending tasks. The task
/// will be created with a pending status and will be available for processing
/// via the task_next tool.
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
        context
            .send_text(TitleFormat::debug("TaskAdd").sub_title(&input.description))
            .await?;

        self.infra.task_service().append(input.description).await?;

        // Calculate stats manually
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = TaskListResult {
            message: Some("Task added to the end of the list.".to_string()),
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
    async fn test_add_task() {
        // Create fixture
        let task_add = create_task_add();

        let input = TaskAddInput { description: "Test task".to_string(), explanation: None };

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
}
