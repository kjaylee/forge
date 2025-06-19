use std::sync::Arc;

use anyhow::Result;
use forge_app::{TaskListInput, TaskListOutput, TaskListService, TaskOperation};

use crate::TaskService;

/// Task list management tool for organizing and tracking work items.
/// Supports operations like append, prepend, pop, mark done, list, clear, and
/// stats. Tasks are stored in conversation state and persist across agent
/// interactions.
pub struct ForgeTaskList {
    task_service: Arc<std::sync::RwLock<TaskService>>,
}

impl ForgeTaskList {
    pub fn new(task_service: Arc<std::sync::RwLock<TaskService>>) -> Self {
        Self { task_service }
    }
}

#[async_trait::async_trait]
impl TaskListService for ForgeTaskList {
    async fn execute_task_list(&self, input: TaskListInput) -> Result<TaskListOutput> {
        let mut service = self.task_service.write().unwrap();

        match input.operation {
            TaskOperation::Append { task } => {
                let (created_task, stats) = service.append(task)?;
                Ok(TaskListOutput::TaskAdded {
                    task: created_task,
                    stats,
                    message: "Task appended to the list.".to_string(),
                })
            }
            TaskOperation::Prepend { task } => {
                let (created_task, stats) = service.prepend(task)?;
                Ok(TaskListOutput::TaskAdded {
                    task: created_task,
                    stats,
                    message: "Task prepended to the list.".to_string(),
                })
            }
            TaskOperation::PopFront => {
                if let Some((task, stats)) = service.pop_front()? {
                    Ok(TaskListOutput::TaskPopped {
                        task,
                        stats,
                        message: "Task popped from front and marked as IN_PROGRESS.".to_string(),
                    })
                } else {
                    Ok(TaskListOutput::Empty { message: "No tasks available to pop.".to_string() })
                }
            }
            TaskOperation::PopBack => {
                if let Some((task, stats)) = service.pop_back()? {
                    Ok(TaskListOutput::TaskPopped {
                        task,
                        stats,
                        message: "Task popped from back and marked as IN_PROGRESS.".to_string(),
                    })
                } else {
                    Ok(TaskListOutput::Empty { message: "No tasks available to pop.".to_string() })
                }
            }
            TaskOperation::MarkDone { task_id } => {
                if let Some((completed_task, next_task, stats)) = service.mark_done(task_id)? {
                    let message = if let Some(next) = &next_task {
                        format!(
                            "Task '{}' marked as DONE. Next pending task: '{}'",
                            completed_task.task, next.task
                        )
                    } else {
                        format!(
                            "Task '{}' marked as DONE. No more pending tasks.",
                            completed_task.task
                        )
                    };

                    Ok(TaskListOutput::TaskCompleted { completed_task, next_task, stats, message })
                } else {
                    Ok(TaskListOutput::Error {
                        message: format!("Task with ID {task_id} not found."),
                    })
                }
            }
            TaskOperation::List => {
                let markdown = service.to_markdown();
                let stats = service.stats();
                Ok(TaskListOutput::TaskList { markdown, stats })
            }
            TaskOperation::Clear => {
                service.clear()?;
                Ok(TaskListOutput::Cleared {
                    message: "All tasks cleared from the list.".to_string(),
                })
            }
            TaskOperation::Stats => {
                let stats = service.stats();
                Ok(TaskListOutput::StatsOnly { stats })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use pretty_assertions::assert_eq;

    use super::*;

    fn create_fixture() -> ForgeTaskList {
        let task_service = Arc::new(RwLock::new(TaskService::new()));
        ForgeTaskList::new(task_service)
    }

    #[tokio::test]
    async fn test_append_task() {
        let tool = create_fixture();
        let input = TaskListInput {
            operation: TaskOperation::Append { task: "Test task".to_string() },
        };

        let result = tool.execute_task_list(input).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::TaskAdded { task, stats, message } => {
                assert_eq!(task.task, "Test task");
                assert_eq!(stats.total_tasks, 1);
                assert_eq!(stats.pending_tasks, 1);
                assert_eq!(message, "Task appended to the list.");
            }
            _ => panic!("Expected TaskAdded output"),
        }
    }

    #[tokio::test]
    async fn test_prepend_task() {
        let tool = create_fixture();

        // First add a task
        let input1 = TaskListInput {
            operation: TaskOperation::Append { task: "Second task".to_string() },
        };
        tool.execute_task_list(input1).await.unwrap();

        // Then prepend another
        let input2 = TaskListInput {
            operation: TaskOperation::Prepend { task: "First task".to_string() },
        };

        let result = tool.execute_task_list(input2).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::TaskAdded { task, stats, message } => {
                assert_eq!(task.task, "First task");
                assert_eq!(stats.total_tasks, 2);
                assert_eq!(message, "Task prepended to the list.");
            }
            _ => panic!("Expected TaskAdded output"),
        }
    }

    #[tokio::test]
    async fn test_pop_front() {
        let tool = create_fixture();

        // Add tasks first
        let input1 = TaskListInput {
            operation: TaskOperation::Append { task: "Task 1".to_string() },
        };
        tool.execute_task_list(input1).await.unwrap();

        let input2 = TaskListInput {
            operation: TaskOperation::Append { task: "Task 2".to_string() },
        };
        tool.execute_task_list(input2).await.unwrap();

        // Pop front
        let input3 = TaskListInput { operation: TaskOperation::PopFront };

        let result = tool.execute_task_list(input3).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::TaskPopped { task, stats, message } => {
                assert_eq!(task.task, "Task 1");
                assert!(task.is_in_progress());
                assert_eq!(stats.total_tasks, 1);
                assert_eq!(message, "Task popped from front and marked as IN_PROGRESS.");
            }
            _ => panic!("Expected TaskPopped output"),
        }
    }

    #[tokio::test]
    async fn test_mark_done() {
        let tool = create_fixture();

        // Add tasks first
        let input1 = TaskListInput {
            operation: TaskOperation::Append { task: "Task 1".to_string() },
        };
        let result1 = tool.execute_task_list(input1).await.unwrap();
        let task_id = match result1 {
            TaskListOutput::TaskAdded { task, .. } => task.id,
            _ => panic!("Expected TaskAdded output"),
        };

        let input2 = TaskListInput {
            operation: TaskOperation::Append { task: "Task 2".to_string() },
        };
        tool.execute_task_list(input2).await.unwrap();

        // Mark first task as done
        let input3 = TaskListInput { operation: TaskOperation::MarkDone { task_id } };

        let result = tool.execute_task_list(input3).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::TaskCompleted { completed_task, next_task, stats, message } => {
                assert_eq!(completed_task.task, "Task 1");
                assert!(completed_task.is_done());
                assert!(next_task.is_some());
                assert_eq!(next_task.unwrap().task, "Task 2");
                assert_eq!(stats.done_tasks, 1);
                assert!(message.contains("Task 'Task 1' marked as DONE"));
            }
            _ => panic!("Expected TaskCompleted output"),
        }
    }

    #[tokio::test]
    async fn test_list_tasks() {
        let tool = create_fixture();

        // Add a task first
        let input1 = TaskListInput {
            operation: TaskOperation::Append { task: "Test task".to_string() },
        };
        tool.execute_task_list(input1).await.unwrap();

        // List tasks
        let input2 = TaskListInput { operation: TaskOperation::List };

        let result = tool.execute_task_list(input2).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::TaskList { markdown, stats } => {
                assert!(markdown.contains("# Task List"));
                assert!(markdown.contains("Test task"));
                assert_eq!(stats.total_tasks, 1);
            }
            _ => panic!("Expected TaskList output"),
        }
    }

    #[tokio::test]
    async fn test_clear_tasks() {
        let tool = create_fixture();

        // Add tasks first
        let input1 = TaskListInput {
            operation: TaskOperation::Append { task: "Task 1".to_string() },
        };
        tool.execute_task_list(input1).await.unwrap();

        // Clear tasks
        let input2 = TaskListInput { operation: TaskOperation::Clear };

        let result = tool.execute_task_list(input2).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::Cleared { message } => {
                assert_eq!(message, "All tasks cleared from the list.");
            }
            _ => panic!("Expected Cleared output"),
        }
    }

    #[tokio::test]
    async fn test_empty_pop() {
        let tool = create_fixture();

        let input = TaskListInput { operation: TaskOperation::PopFront };

        let result = tool.execute_task_list(input).await;

        assert!(result.is_ok());
        match result.unwrap() {
            TaskListOutput::Empty { message } => {
                assert_eq!(message, "No tasks available to pop.");
            }
            _ => panic!("Expected Empty output"),
        }
    }
}
