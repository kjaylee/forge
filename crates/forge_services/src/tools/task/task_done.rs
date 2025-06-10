use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_display::TitleFormat;
use forge_domain::{
    ExecutableTool, NamedTool, TaskDoneInput, ToolCallContext, ToolDescription, ToolName,
    ToolOutput,
};
use forge_tool_macros::ToolDescription;

use crate::task::TaskListResult;
use crate::Infrastructure;

/// Mark a task as completed by its ID. This tool updates a specific task's
/// status to Done and identifies the next pending task for processing. Use this
/// when you have finished working on a task and want to mark it as complete.
/// The tool will automatically find and return the next available pending task,
/// helping maintain workflow continuity. If the specified task ID is not found,
/// an appropriate error message will be returned.
#[derive(Debug, ToolDescription)]
pub struct TaskDone<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskDone<F> {
    /// Creates a new TaskDone tool with the given infrastructure.
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F> NamedTool for TaskDone<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_task_done")
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for TaskDone<F> {
    type Input = TaskDoneInput;

    async fn call(&self, context: &mut ToolCallContext, input: Self::Input) -> Result<ToolOutput> {
        context
            .send_text(TitleFormat::debug("TaskDone").sub_title(input.task_id.to_string()))
            .await?;

        let found_task = self
            .infra
            .task_service()
            .mark_done(input.task_id.clone())
            .await?;

        if found_task.is_none() {
            // Calculate stats manually
            let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
                self.infra.task_service().stats().await?;

            let stats =
                crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

            let result = TaskListResult {
                message: Some(format!("No task found with ID {}.", input.task_id)),
                next_task: None,
                stats,
                tasks: None,
            };

            return Ok(ToolOutput::text(result.to_string()));
        }

        let next_task = self.infra.task_service().find_next_pending().await?;

        // Calculate stats manually
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        let stats =
            crate::task::Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks };

        let result = TaskListResult {
            message: if next_task.is_some() {
                Some(format!(
                    "Task {} marked as done. Next taskId is {}.",
                    input.task_id,
                    next_task.as_ref().unwrap().id
                ))
            } else {
                Some(format!(
                    "Task {} marked as done. No more pending tasks.",
                    input.task_id
                ))
            },
            next_task,
            stats,
            tasks: None,
        };

        Ok(ToolOutput::text(result.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use forge_domain::{TaskId, ToolCallContext};

    use super::*;
    use crate::attachment::tests::MockInfrastructure;

    fn create_task_done() -> TaskDone<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskDone::new(infra)
    }

    #[tokio::test]
    async fn test_task_done_not_found() {
        // Create fixture
        let task_done = create_task_done();

        let input = TaskDoneInput { task_id: TaskId::from_u64(0), explanation: None };

        // Execute the fixture
        let result = task_done
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }
}
