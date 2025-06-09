use std::fmt::Display;
use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_display::TitleFormat;
use forge_domain::{
    ExecutableTool, NamedTool, Operation, OperationType, Task, TaskId, ToolCallContext,
    ToolDescription, ToolName, ToolOutput,
};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::Infrastructure;

/// Statistics about the TaskList.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq)]
pub struct Stats {
    /// Total number of tasks in the list.
    pub total_tasks: u32,
    /// Number of completed tasks.
    pub done_tasks: u32,
    /// Number of pending tasks.
    pub pending_tasks: u32,
    /// Number of in-progress tasks.
    pub in_progress_tasks: u32,
}

impl std::fmt::Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<stats>\n<total_tasks>{}</total_tasks>\n<done_tasks>{}</done_tasks>\n<pending_tasks>{}</pending_tasks>\n<in_progress_tasks>{}</in_progress_tasks>\n</stats>",
            self.total_tasks, self.done_tasks, self.pending_tasks, self.in_progress_tasks)
    }
}

/// TaskList operation result.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TaskListResult {
    /// Message describing the result of the operation.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    /// The task that was affected by the operation, if applicable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub next_task: Option<Task>,
    /// Statistics about the task list.
    pub stats: Stats,
    /// List of tasks
    pub tasks: Option<Vec<Task>>,
}

impl Display for TaskListResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = String::from("<task_list_result>\n");

        if let Some(message) = &self.message {
            result.push_str(&format!("<message>{message}</message>\n"));
        }

        if let Some(task) = &self.next_task {
            result.push_str("<next_task>\n");
            result.push_str(&format!("{task}\n"));
            result.push_str("\n</next_task>\n");
        }

        result.push_str(&format!("{}\n", self.stats));

        if let Some(tasks) = &self.tasks {
            if !tasks.is_empty() {
                result.push_str("<tasks_list>\n");
                for task in tasks {
                    result.push_str(&format!("{task}\n"));
                }
                result.push_str("</tasks_list>\n");
            }
        }

        result.push_str("</task_list_result>");

        write!(f, "{result}")
    }
}

/// A stateful task management tool that maintains an ordered list of tasks with
/// status tracking. Provides operations to add tasks (append/prepend), mark
/// tasks as in-progress (pop_front/pop_back), complete tasks (mark_done), and
/// view the current state (list). Automatically identifies the next pending
/// task when completing items and provides detailed statistics on task status.
/// Ideal for sequential workflows, project planning, and tracking multi-step
/// processes.
#[derive(Debug, ToolDescription)]
pub struct TaskList<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskList<F> {
    /// Creates a new TaskList tool with the given infrastructure.
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }

    /// Calculate statistics for the current task list.
    async fn calculate_stats(&self) -> Result<Stats> {
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        Ok(Stats { total_tasks, done_tasks, pending_tasks, in_progress_tasks })
    }

    /// Handle the append operation, adding a task to the end of the list.
    async fn append(&self, description: String) -> Result<TaskListResult> {
        self.infra.task_service().append(description).await?;

        let stats = self.calculate_stats().await?;

        Ok(TaskListResult {
            message: Some("Task added to the end of the list.".to_string()),
            next_task: None,
            stats,
            tasks: None,
        })
    }

    /// Handle the prepend operation, adding a task to the beginning of the
    /// list.
    async fn prepend(&self, description: String) -> Result<TaskListResult> {
        self.infra.task_service().prepend(description).await?;

        let stats = self.calculate_stats().await?;

        Ok(TaskListResult {
            message: Some("Task added to the beginning of the list.".to_string()),
            next_task: None,
            stats,
            tasks: None,
        })
    }

    /// Handle the pop_front operation, marking the first pending task as
    /// InProgress without removing it.
    async fn pop_front(&self) -> Result<TaskListResult> {
        let task_option = self.infra.task_service().pop_front().await?;

        let stats = self.calculate_stats().await?;

        if let Some(task) = task_option {
            Ok(TaskListResult { message: None, next_task: Some(task), stats, tasks: None })
        } else {
            Ok(TaskListResult {
                message: Some("No pending tasks found.".to_string()),
                next_task: None,
                stats,
                tasks: None,
            })
        }
    }

    /// Handle the mark_done operation, marking a task as completed and finding
    /// the next pending task.
    async fn mark_done(&self, id: TaskId) -> Result<TaskListResult> {
        let found_task = self.infra.task_service().mark_done(id.clone()).await?;

        if found_task.is_none() {
            return Ok(TaskListResult {
                message: Some(format!("No task found with ID {id}.")),
                next_task: None,
                stats: self.calculate_stats().await?,
                tasks: None,
            });
        }

        let next_task = self.infra.task_service().find_next_pending().await?;
        let stats = self.calculate_stats().await?;

        Ok(TaskListResult {
            message: if next_task.is_some() {
                Some(format!(
                    "Task {} marked as done. Next taskId is {}.",
                    id,
                    next_task.as_ref().unwrap().id
                ))
            } else {
                Some(format!("Task {id} marked as done. No more pending tasks."))
            },
            next_task,
            stats,
            tasks: None,
        })
    }

    /// Handle the list operation, returning all tasks in markdown format.
    async fn list(&self) -> Result<TaskListResult> {
        let tasks = self.infra.task_service().list().await?;
        let stats = self.calculate_stats().await?;
        let markdown = self.infra.task_service().format_markdown().await?;

        // Use TaskDisplayService for consistent formatting

        Ok(TaskListResult {
            message: Some(markdown),
            next_task: None,
            stats,
            tasks: Some(tasks),
        })
    }
}

impl<F> NamedTool for TaskList<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_task_list")
    }
}

fn format_input(input: &Operation) -> String {
    match input.operation_type {
        OperationType::Append => {
            format!(
                "Append: {}",
                input
                    .description
                    .as_ref()
                    .unwrap_or(&"<missing description>".to_string())
            )
        }
        OperationType::Prepend => {
            format!(
                "Prepend: {}",
                input
                    .description
                    .as_ref()
                    .unwrap_or(&"<missing description>".to_string())
            )
        }
        OperationType::Next => "Next".to_string(),
        OperationType::Done => {
            format!("Done: {}", input.task_id.as_ref().unwrap_or(&TaskId::new()))
        }
        OperationType::List => "List".to_string(),
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for TaskList<F> {
    type Input = Operation;

    async fn call(&self, context: &mut ToolCallContext, input: Self::Input) -> Result<ToolOutput> {
        context
            .send_text(TitleFormat::debug("TaskList").sub_title(format_input(&input)))
            .await?;

        let result = match input.operation_type {
            OperationType::Append => {
                let description = input
                    .description
                    .ok_or_else(|| anyhow::anyhow!("Description required for append operation"))?;
                self.append(description).await?
            }
            OperationType::Prepend => {
                let description = input
                    .description
                    .ok_or_else(|| anyhow::anyhow!("Description required for prepend operation"))?;
                self.prepend(description).await?
            }
            OperationType::Next => self.pop_front().await?,
            OperationType::Done => {
                let task_id = input
                    .task_id
                    .ok_or_else(|| anyhow::anyhow!("Task ID required for done operation"))?;
                self.mark_done(task_id).await?
            }
            OperationType::List => self.list().await?,
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

    fn create_task_list() -> TaskList<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskList::new(infra)
    }

    #[tokio::test]
    async fn test_append_task() {
        // Create fixture
        let task_list = create_task_list();

        let input = Operation::append("Test task".to_string());

        // Execute the fixture
        let result = task_list
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_prepend_task() {
        // Create fixture
        let task_list = create_task_list();

        let input1 = Operation::append("Task 1".to_string());
        let input2 = Operation::prepend("Task 2".to_string());

        // Execute the fixture
        task_list
            .call(&mut ToolCallContext::default(), input1)
            .await
            .unwrap();
        let result = task_list
            .call(&mut ToolCallContext::default(), input2)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_pop_front() {
        // Create fixture
        let task_list = create_task_list();

        let input1 = Operation::append("Task to pop".to_string());
        let input2 = Operation::next();

        // Execute the fixture
        task_list
            .call(&mut ToolCallContext::default(), input1)
            .await
            .unwrap();
        let result = task_list
            .call(&mut ToolCallContext::default(), input2)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_mark_done() {
        // Create fixture
        let task_list = create_task_list();
        let input1 = Operation::append("Task to mark done".to_string());

        // Execute the fixture - first add a task
        task_list
            .call(&mut ToolCallContext::default(), input1)
            .await
            .unwrap();

        // Get the task ID from the service (we know it will be deterministic)
        let tasks = task_list.infra.task_service().list().await.unwrap();
        let task_id = tasks[0].id.clone();

        // Mark the task as done
        let input2 = Operation::done(task_id);
        let result = task_list
            .call(&mut ToolCallContext::default(), input2)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_empty_list() {
        // Create fixture
        let task_list = create_task_list();
        let input = Operation::next();

        // Execute the fixture
        let actual = task_list
            .call(&mut ToolCallContext::default(), input)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(actual);
    }

    #[tokio::test]
    async fn test_list_operation() {
        // Create fixture
        let task_list = create_task_list();

        // Add some tasks first
        let input1 = Operation::append("Task 1".to_string());
        let input2 = Operation::append("Task 2".to_string());
        let input3 = Operation::list();

        // Execute the fixture
        task_list
            .call(&mut ToolCallContext::default(), input1)
            .await
            .unwrap();
        task_list
            .call(&mut ToolCallContext::default(), input2)
            .await
            .unwrap();

        let result = task_list
            .call(&mut ToolCallContext::default(), input3)
            .await
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();

        insta::assert_snapshot!(result);
    }
}
