use std::collections::VecDeque;

use derive_setters::Setters;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum Status {
    #[default]
    Pending,
    InProgress,
    Done,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Setters)]
#[setters(strip_option, into)]
pub struct Task {
    pub id: u32,
    pub task: String,
    pub status: Status,
}

impl Task {
    pub fn new(id: u32, task: impl Into<String>) -> Self {
        Self { id, task: task.into(), status: Status::default() }
    }

    pub fn mark_in_progress(&mut self) -> &mut Self {
        self.status = Status::InProgress;
        self
    }

    pub fn mark_done(&mut self) -> &mut Self {
        self.status = Status::Done;
        self
    }

    pub fn is_pending(&self) -> bool {
        matches!(self.status, Status::Pending)
    }

    pub fn is_in_progress(&self) -> bool {
        matches!(self.status, Status::InProgress)
    }

    pub fn is_done(&self) -> bool {
        matches!(self.status, Status::Done)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaskStats {
    pub total_tasks: u32,
    pub done_tasks: u32,
    pub pending_tasks: u32,
    pub in_progress_tasks: u32,
}

impl TaskStats {
    fn new(total_tasks: u32, done_tasks: u32, pending_tasks: u32, in_progress_tasks: u32) -> Self {
        Self { total_tasks, done_tasks, pending_tasks, in_progress_tasks }
    }

    pub fn from_tasks(tasks: &VecDeque<Task>) -> Self {
        let total_tasks = tasks.len() as u32;
        let done_tasks = tasks.iter().filter(|t| t.is_done()).count() as u32;
        let pending_tasks = tasks.iter().filter(|t| t.is_pending()).count() as u32;
        let in_progress_tasks = tasks.iter().filter(|t| t.is_in_progress()).count() as u32;

        Self::new(total_tasks, done_tasks, pending_tasks, in_progress_tasks)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct TaskList {
    tasks: VecDeque<Task>,
    next_id: u32,
}

impl TaskList {
    pub fn new() -> Self {
        Self { tasks: VecDeque::new(), next_id: 1 }
    }

    pub fn append(&mut self, task: impl Into<String>) -> (Task, TaskStats) {
        let task = Task::new(self.next_id, task);
        self.next_id += 1;
        self.tasks.push_back(task.clone());
        let stats = self.stats();
        (task, stats)
    }

    pub fn prepend(&mut self, task: impl Into<String>) -> (Task, TaskStats) {
        let task = Task::new(self.next_id, task);
        self.next_id += 1;
        self.tasks.push_front(task.clone());
        let stats = self.stats();
        (task, stats)
    }

    pub fn pop_front(&mut self) -> Option<(Task, TaskStats)> {
        if self.tasks.is_empty() {
            return None;
        }

        let mut task = self.tasks.pop_front()?;
        task.mark_in_progress();
        let stats = self.stats();
        Some((task, stats))
    }

    pub fn pop_back(&mut self) -> Option<(Task, TaskStats)> {
        if self.tasks.is_empty() {
            return None;
        }

        let mut task = self.tasks.pop_back()?;
        task.mark_in_progress();
        let stats = self.stats();
        Some((task, stats))
    }

    pub fn mark_done(&mut self, task_id: u32) -> Option<(Task, Option<Task>, TaskStats)> {
        let task_index = self.tasks.iter().position(|t| t.id == task_id)?;
        self.tasks[task_index].mark_done();
        let completed_task = self.tasks[task_index].clone();

        // Find next pending task
        let next_task = self.tasks.iter().find(|t| t.is_pending()).cloned();
        let stats = self.stats();

        Some((completed_task, next_task, stats))
    }

    pub fn stats(&self) -> TaskStats {
        TaskStats::from_tasks(&self.tasks)
    }

    pub fn clear(&mut self) {
        self.tasks.clear();
        self.next_id = 1;
    }

    pub fn to_markdown(&self) -> String {
        if self.tasks.is_empty() {
            return "No tasks in the list.".to_string();
        }

        let mut markdown = String::new();
        markdown.push_str("# Task List\n\n");

        for task in &self.tasks {
            let status_icon = match task.status {
                Status::Pending => "⏳",
                Status::InProgress => "🔄",
                Status::Done => "✅",
            };
            markdown.push_str(&format!(
                "{}. {} {} - {}\n",
                task.id,
                status_icon,
                task.status_name(),
                task.task
            ));
        }

        let stats = self.stats();
        markdown.push_str(&format!(
            "\n**Stats:** {} total, {} done, {} in progress, {} pending\n",
            stats.total_tasks, stats.done_tasks, stats.in_progress_tasks, stats.pending_tasks
        ));

        markdown
    }
}

impl Status {
    pub fn status_name(&self) -> &'static str {
        match self {
            Status::Pending => "PENDING",
            Status::InProgress => "IN_PROGRESS",
            Status::Done => "DONE",
        }
    }
}

impl Task {
    pub fn status_name(&self) -> &'static str {
        self.status.status_name()
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_task_creation() {
        let task = Task::new(1, "Test task");

        assert_eq!(task.id, 1);
        assert_eq!(task.task, "Test task");
        assert_eq!(task.status, Status::Pending);
        assert!(task.is_pending());
    }

    #[test]
    fn test_task_status_transitions() {
        let mut task = Task::new(1, "Test task");

        task.mark_in_progress();
        assert!(task.is_in_progress());

        task.mark_done();
        assert!(task.is_done());
    }

    #[test]
    fn test_stats_from_tasks() {
        let tasks = vec![
            Task::new(1, "Task 1"), // Pending
            Task::new(2, "Task 2").status(Status::InProgress),
            Task::new(3, "Task 3").status(Status::Done),
            Task::new(4, "Task 4"), // Pending
        ]
        .into_iter()
        .collect();

        let stats = TaskStats::from_tasks(&tasks);

        assert_eq!(stats.total_tasks, 4);
        assert_eq!(stats.pending_tasks, 2);
        assert_eq!(stats.in_progress_tasks, 1);
        assert_eq!(stats.done_tasks, 1);
    }

    #[test]
    fn test_task_list_append() {
        let mut task_list = TaskList::new();

        let (task, stats) = task_list.append("First task");

        assert_eq!(task.id, 1);
        assert_eq!(task.task, "First task");
        assert_eq!(stats.total_tasks, 1);
        assert_eq!(stats.pending_tasks, 1);
    }

    #[test]
    fn test_task_list_prepend() {
        let mut task_list = TaskList::new();
        task_list.append("Second task");

        let (task, stats) = task_list.prepend("First task");

        assert_eq!(task.id, 2);
        assert_eq!(task.task, "First task");
        assert_eq!(task_list.tasks[0].task, "First task");
        assert_eq!(stats.total_tasks, 2);
    }

    #[test]
    fn test_task_list_pop_front() {
        let mut task_list = TaskList::new();
        task_list.append("Task 1");
        task_list.append("Task 2");

        let result = task_list.pop_front();

        assert!(result.is_some());
        let (task, stats) = result.unwrap();
        assert_eq!(task.task, "Task 1");
        assert!(task.is_in_progress());
        assert_eq!(stats.total_tasks, 1);
    }

    #[test]
    fn test_task_list_mark_done() {
        let mut task_list = TaskList::new();
        let (task1, _) = task_list.append("Task 1");
        task_list.append("Task 2");

        let result = task_list.mark_done(task1.id);

        assert!(result.is_some());
        let (completed_task, next_task, stats) = result.unwrap();
        assert_eq!(completed_task.task, "Task 1");
        assert!(completed_task.is_done());
        assert!(next_task.is_some());
        assert_eq!(next_task.unwrap().task, "Task 2");
        assert_eq!(stats.done_tasks, 1);
    }

    #[test]
    fn test_task_list_to_markdown() {
        let mut task_list = TaskList::new();
        task_list.append("Task 1");
        let (task2, _) = task_list.append("Task 2");
        task_list.mark_done(task2.id);

        let markdown = task_list.to_markdown();

        assert!(markdown.contains("# Task List"));
        assert!(markdown.contains("⏳ PENDING - Task 1"));
        assert!(markdown.contains("✅ DONE - Task 2"));
        assert!(markdown.contains("**Stats:**"));
    }

    #[test]
    fn test_empty_task_list_markdown() {
        let task_list = TaskList::new();
        let markdown = task_list.to_markdown();

        assert_eq!(markdown, "No tasks in the list.");
    }
}
