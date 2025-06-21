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

impl From<&TaskList> for TaskStats {
    fn from(task_list: &TaskList) -> Self {
        Self::from_tasks(&task_list.tasks)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct TaskList {
    pub tasks: VecDeque<Task>,
    next_id: u32,
}

impl TaskList {
    pub fn new() -> Self {
        Self { tasks: VecDeque::new(), next_id: 1 }
    }

    pub fn append(&mut self, task: impl Into<String>) -> Task {
        let task = Task::new(self.next_id, task);
        self.next_id += 1;
        self.tasks.push_back(task.clone());
        task
    }

    pub fn mark_done(&mut self, task_id: u32) -> Option<Task> {
        let task_index = self.tasks.iter().position(|t| t.id == task_id)?;
        self.tasks[task_index].mark_done();
        Some(self.tasks[task_index].clone())
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

        // Calculate the width needed for padding based on the highest task ID
        let max_id_width = self
            .tasks
            .iter()
            .map(|task| task.id.to_string().len())
            .max()
            .unwrap_or(1);

        for task in &self.tasks {
            let formatted_task = match task.status {
                Status::Pending => {
                    format!("{:width$}. {}\n", task.id, task.task, width = max_id_width)
                }
                Status::InProgress => {
                    format!(
                        "{:width$}. **{}**\n",
                        task.id,
                        task.task,
                        width = max_id_width
                    )
                }
                Status::Done => {
                    format!(
                        "{:width$}. ~~{}~~\n",
                        task.id,
                        task.task,
                        width = max_id_width
                    )
                }
            };
            markdown.push_str(&formatted_task);
        }

        let stats = TaskStats::from(self);
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
    fn test_stats_from_task_list() {
        let mut task_list = TaskList::new();
        task_list.append("Task 1"); // Pending
        let task2 = task_list.append("Task 2");
        task_list.append("Task 3"); // Pending
        task_list.mark_done(task2.id); // Mark task 2 as done

        let stats = TaskStats::from(&task_list);

        assert_eq!(stats.total_tasks, 3);
        assert_eq!(stats.pending_tasks, 2);
        assert_eq!(stats.in_progress_tasks, 0);
        assert_eq!(stats.done_tasks, 1);
    }

    #[test]
    fn test_task_list_append() {
        let mut task_list = TaskList::new();

        let task = task_list.append("First task");

        assert_eq!(task.id, 1);
        assert_eq!(task.task, "First task");
        assert_eq!(task_list.tasks.len(), 1);
    }

    #[test]
    fn test_task_list_mark_done() {
        let mut task_list = TaskList::new();
        let task1 = task_list.append("Task 1");
        task_list.append("Task 2");

        let result = task_list.mark_done(task1.id);

        assert!(result.is_some());
        let completed_task = result.unwrap();
        assert_eq!(completed_task.task, "Task 1");
        assert!(completed_task.is_done());
    }

    #[test]
    fn test_task_list_mark_done_nonexistent() {
        let mut task_list = TaskList::new();
        task_list.append("Task 1");

        let result = task_list.mark_done(999);

        assert!(result.is_none());
    }

    #[test]
    fn test_task_list_clear() {
        let mut task_list = TaskList::new();
        task_list.append("Task 1");
        task_list.append("Task 2");

        task_list.clear();

        assert!(task_list.tasks.is_empty());
        assert_eq!(task_list.next_id, 1);
    }

    #[test]
    fn test_task_list_to_markdown() {
        let mut task_list = TaskList::new();
        task_list.append("Task 1");
        let task2 = task_list.append("Task 2");
        task_list.mark_done(task2.id);

        let markdown = task_list.to_markdown();

        assert!(markdown.contains("# Task List"));
        assert!(markdown.contains("1. Task 1"));
        assert!(markdown.contains("~~Task 2~~"));
        assert!(markdown.contains("**Stats:**"));
    }

    #[test]
    fn test_empty_task_list_markdown() {
        let task_list = TaskList::new();
        let markdown = task_list.to_markdown();

        assert_eq!(markdown, "No tasks in the list.");
    }

    // Snapshot tests for markdown output
    #[test]
    fn test_empty_task_list_markdown_snapshot() {
        let fixture = TaskList::new();
        let actual = fixture.to_markdown();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn test_single_pending_task_markdown_snapshot() {
        let mut fixture = TaskList::new();
        fixture.append("Write documentation");
        let actual = fixture.to_markdown();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn test_mixed_status_tasks_markdown_snapshot() {
        let mut fixture = TaskList::new();
        let _task1 = fixture.append("First task");
        let task2 = fixture.append("Second task");
        fixture.append("Third task");

        // Mark second task as done
        fixture.mark_done(task2.id);

        // Mark first task as in progress manually
        fixture.tasks[0].mark_in_progress();

        let actual = fixture.to_markdown();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn test_all_done_tasks_markdown_snapshot() {
        let mut fixture = TaskList::new();
        let task1 = fixture.append("Complete feature A");
        let task2 = fixture.append("Write tests");
        let task3 = fixture.append("Update documentation");

        fixture.mark_done(task1.id);
        fixture.mark_done(task2.id);
        fixture.mark_done(task3.id);

        let actual = fixture.to_markdown();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn test_complex_task_list_markdown_snapshot() {
        let mut fixture = TaskList::new();
        let _task1 = fixture.append("Review pull request #123");
        let _task2 = fixture.append("Fix bug in authentication");
        let task3 = fixture.append("Deploy to staging");
        let _task4 = fixture.append("Update API documentation");
        let _task5 = fixture.append("Refactor user service");

        // Mark one task as done
        fixture.mark_done(task3.id);

        // Mark two tasks as in progress manually (without removing them)
        fixture.tasks[0].mark_in_progress(); // "Review pull request #123"
        fixture.tasks[4].mark_in_progress(); // "Refactor user service"

        let actual = fixture.to_markdown();
        insta::assert_snapshot!(actual);
    }
}
