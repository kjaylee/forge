use std::sync::{Arc, Mutex};

use anyhow::Result;
use async_trait::async_trait;
use forge_app::TaskService;
use forge_domain::{Task, TaskId, TaskStatus};

#[derive(Clone)]
pub struct ForgeTaskService {
    tasks: Arc<Mutex<Vec<Task>>>,
}

impl ForgeTaskService {
    pub fn new() -> Self {
        Self { tasks: Arc::new(Mutex::new(Vec::new())) }
    }
}

impl Default for ForgeTaskService {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl TaskService for ForgeTaskService {
    async fn append(&self, description: String) -> Result<()> {
        let mut tasks = self.tasks.lock().unwrap();
        let task = Task::new(description);
        tasks.push(task);
        Ok(())
    }

    async fn prepend(&self, description: String) -> Result<()> {
        let mut tasks = self.tasks.lock().unwrap();
        let task = Task::new(description);
        tasks.insert(0, task);
        Ok(())
    }

    async fn pop_front(&self) -> Result<Option<Task>> {
        let mut tasks = self.tasks.lock().unwrap();
        if tasks.is_empty() {
            Ok(None)
        } else {
            let pending_index = tasks
                .iter()
                .position(|task| task.status == TaskStatus::Pending);

            if let Some(index) = pending_index {
                tasks[index].status = TaskStatus::InProgress;
                Ok(Some(tasks[index].clone()))
            } else {
                Ok(None)
            }
        }
    }

    async fn pop_back(&self) -> Result<Option<Task>> {
        let mut tasks = self.tasks.lock().unwrap();
        if tasks.is_empty() {
            Ok(None)
        } else {
            let pending_index = tasks
                .iter()
                .rposition(|task| task.status == TaskStatus::Pending);

            if let Some(index) = pending_index {
                tasks[index].status = TaskStatus::InProgress;
                Ok(Some(tasks[index].clone()))
            } else {
                Ok(None)
            }
        }
    }

    async fn mark_done(&self, id: TaskId) -> Result<Option<Task>> {
        let mut tasks = self.tasks.lock().unwrap();
        for task in tasks.iter_mut() {
            if task.id == id {
                task.status = TaskStatus::Done;
                return Ok(Some(task.clone()));
            }
        }
        Ok(None)
    }

    async fn list(&self) -> Result<Vec<Task>> {
        let tasks = self.tasks.lock().unwrap();
        Ok(tasks.clone())
    }

    async fn stats(&self) -> Result<(u32, u32, u32, u32)> {
        let tasks = self.tasks.lock().unwrap();
        let total = tasks.len() as u32;
        let done = tasks
            .iter()
            .filter(|t| t.status == TaskStatus::Done)
            .count() as u32;
        let pending = tasks
            .iter()
            .filter(|t| t.status == TaskStatus::Pending)
            .count() as u32;
        let in_progress = tasks
            .iter()
            .filter(|t| t.status == TaskStatus::InProgress)
            .count() as u32;
        Ok((total, done, pending, in_progress))
    }

    async fn find_next_pending(&self) -> Result<Option<Task>> {
        let tasks = self.tasks.lock().unwrap();
        Ok(tasks
            .iter()
            .find(|t| t.status == TaskStatus::Pending)
            .cloned())
    }

    async fn format_markdown(&self) -> Result<String> {
        let tasks = self.tasks.lock().unwrap();

        if tasks.is_empty() {
            return Ok("No tasks available.".to_string());
        }

        let mut markdown = String::new();
        let mut sorted_tasks = tasks.clone();
        sorted_tasks.sort_by_key(|task| task.id.clone());

        for task in sorted_tasks {
            let checkbox = match task.status {
                TaskStatus::Done => "[x]",
                TaskStatus::Pending => "[ ]",
                TaskStatus::InProgress => "[ ]",
            };

            let formatted_task = match task.status {
                TaskStatus::Done => format!("- {} {}", checkbox, task.description),
                TaskStatus::Pending => format!("- {} {}", checkbox, task.description),
                TaskStatus::InProgress => {
                    format!("- {} __{} (In Progress)__ ", checkbox, task.description)
                }
            };

            markdown.push_str(&formatted_task);
            markdown.push('\n');
        }

        Ok(markdown)
    }
}
