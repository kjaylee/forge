use std::sync::Arc;

use anyhow::Result;
use forge_app::TaskService;
use forge_domain::TaskStatus;

use crate::Infrastructure;

/// Service for formatting tasks for display in user commands.
/// This service provides beautiful formatting for task lists that can be used
/// by user commands like /tasks, separate from the TaskList tool which outputs
/// XML format for AI agents.
#[derive(Clone, Debug)]
pub struct TaskDisplayService<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TaskDisplayService<F> {
    /// Creates a new TaskDisplayService with the provided infrastructure
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }

    /// Format the current task list as beautiful markdown for user display
    pub async fn format_task_list(&self) -> Result<String> {
        let tasks = self.infra.task_service().list().await?;
        let (total_tasks, done_tasks, pending_tasks, in_progress_tasks) =
            self.infra.task_service().stats().await?;

        // Generate markdown format
        let mut markdown = String::from("# Task List\n\n");

        if tasks.is_empty() {
            markdown.push_str("*No tasks in the list.*\n\n");
        } else {
            // Group tasks by status
            let pending_tasks_list: Vec<_> = tasks
                .iter()
                .filter(|t| matches!(t.status, TaskStatus::Pending))
                .collect();
            let in_progress_tasks_list: Vec<_> = tasks
                .iter()
                .filter(|t| matches!(t.status, TaskStatus::InProgress))
                .collect();
            let done_tasks_list: Vec<_> = tasks
                .iter()
                .filter(|t| matches!(t.status, TaskStatus::Done))
                .collect();

            if !pending_tasks_list.is_empty() {
                markdown.push_str("## 📋 Pending Tasks\n\n");
                for (i, task) in pending_tasks_list.iter().enumerate() {
                    markdown.push_str(&format!(
                        "{}. [ ] {} `{}`\n",
                        i + 1,
                        task.description,
                        task.id
                    ));
                }
                markdown.push('\n');
            }

            if !in_progress_tasks_list.is_empty() {
                markdown.push_str("## 🚧 In Progress\n\n");
                for (i, task) in in_progress_tasks_list.iter().enumerate() {
                    markdown.push_str(&format!(
                        "{}. [⚡] {} `{}`\n",
                        i + 1,
                        task.description,
                        task.id
                    ));
                }
                markdown.push('\n');
            }

            if !done_tasks_list.is_empty() {
                markdown.push_str("## ✅ Completed Tasks\n\n");
                for (i, task) in done_tasks_list.iter().enumerate() {
                    markdown.push_str(&format!(
                        "{}. [x] {} `{}`\n",
                        i + 1,
                        task.description,
                        task.id
                    ));
                }
                markdown.push('\n');
            }
        }

        // Add summary
        markdown.push_str("## 📊 Summary\n\n");
        markdown.push_str(&format!("- **Total Tasks:** {total_tasks}\n"));
        markdown.push_str(&format!("- **Pending:** {pending_tasks}\n"));
        markdown.push_str(&format!("- **In Progress:** {in_progress_tasks}\n"));
        markdown.push_str(&format!("- **Completed:** {done_tasks}\n"));

        Ok(markdown)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use pretty_assertions::assert_eq;

    use super::*;
    use crate::attachment::tests::MockInfrastructure;

    fn create_task_display_service() -> TaskDisplayService<MockInfrastructure> {
        let infra = Arc::new(MockInfrastructure::new());
        TaskDisplayService::new(infra)
    }

    #[tokio::test]
    async fn test_format_empty_task_list() {
        // Create fixture
        let service = create_task_display_service();

        // Execute the fixture
        let actual = service.format_task_list().await.unwrap();

        // Define expected result
        let expected = "# Task List\n\n*No tasks in the list.*\n\n## 📊 Summary\n\n- **Total Tasks:** 0\n- **Pending:** 0\n- **In Progress:** 0\n- **Completed:** 0\n";

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }
}
