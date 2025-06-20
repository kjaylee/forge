use anyhow::Result;
use forge_domain::{Stats, Task, TaskList};

#[derive(Debug, Clone)]
pub struct TaskService {
    task_list: TaskList,
}

impl TaskService {
    pub fn new() -> Self {
        Self { task_list: TaskList::new() }
    }

    pub fn append(&mut self, task: impl Into<String>) -> Result<(Task, Stats)> {
        let result = self.task_list.append(task);
        Ok(result)
    }

    pub fn prepend(&mut self, task: impl Into<String>) -> Result<(Task, Stats)> {
        let result = self.task_list.prepend(task);
        Ok(result)
    }

    pub fn pop_front(&mut self) -> Result<Option<(Task, Stats)>> {
        Ok(self.task_list.pop_front())
    }

    pub fn pop_back(&mut self) -> Result<Option<(Task, Stats)>> {
        Ok(self.task_list.pop_back())
    }

    pub fn mark_done(&mut self, task_id: u32) -> Result<Option<(Task, Option<Task>, Stats)>> {
        Ok(self.task_list.mark_done(task_id))
    }

    pub fn stats(&self) -> Stats {
        self.task_list.stats()
    }

    pub fn to_markdown(&self) -> String {
        self.task_list.to_markdown()
    }

    pub fn clear(&mut self) -> Result<()> {
        self.task_list.clear();
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.task_list.is_empty()
    }

    pub fn len(&self) -> usize {
        self.task_list.len()
    }

    pub fn get_task_list(&self) -> &TaskList {
        &self.task_list
    }

    pub fn get_task_list_mut(&mut self) -> &mut TaskList {
        &mut self.task_list
    }

    pub fn set_task_list(&mut self, task_list: TaskList) {
        self.task_list = task_list;
    }
}

impl Default for TaskService {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_task_service_creation() {
        let task_service = TaskService::new();

        assert!(task_service.is_empty());
        assert_eq!(task_service.len(), 0);
    }

    #[test]
    fn test_task_service_append() {
        let mut task_service = TaskService::new();

        let result = task_service.append("Test task");

        assert!(result.is_ok());
        let (task, stats) = result.unwrap();
        assert_eq!(task.task, "Test task");
        assert_eq!(stats.total_tasks, 1);
        assert_eq!(stats.pending_tasks, 1);
    }

    #[test]
    fn test_task_service_prepend() {
        let mut task_service = TaskService::new();
        task_service.append("Second task").unwrap();

        let result = task_service.prepend("First task");

        assert!(result.is_ok());
        let (task, stats) = result.unwrap();
        assert_eq!(task.task, "First task");
        assert_eq!(stats.total_tasks, 2);
    }

    #[test]
    fn test_task_service_pop_front() {
        let mut task_service = TaskService::new();
        task_service.append("Task 1").unwrap();
        task_service.append("Task 2").unwrap();

        let result = task_service.pop_front();

        assert!(result.is_ok());
        let popped = result.unwrap();
        assert!(popped.is_some());
        let (task, stats) = popped.unwrap();
        assert_eq!(task.task, "Task 1");
        assert!(task.is_in_progress());
        assert_eq!(stats.total_tasks, 1);
    }

    #[test]
    fn test_task_service_mark_done() {
        let mut task_service = TaskService::new();
        let (task1, _) = task_service.append("Task 1").unwrap();
        task_service.append("Task 2").unwrap();

        let result = task_service.mark_done(task1.id);

        assert!(result.is_ok());
        let marked = result.unwrap();
        assert!(marked.is_some());
        let (completed_task, next_task, stats) = marked.unwrap();
        assert_eq!(completed_task.task, "Task 1");
        assert!(completed_task.is_done());
        assert!(next_task.is_some());
        assert_eq!(next_task.unwrap().task, "Task 2");
        assert_eq!(stats.done_tasks, 1);
    }

    #[test]
    fn test_task_service_to_markdown() {
        let mut task_service = TaskService::new();
        task_service.append("Task 1").unwrap();
        let (task2, _) = task_service.append("Task 2").unwrap();
        task_service.mark_done(task2.id).unwrap();

        let markdown = task_service.to_markdown();

        assert!(markdown.contains("# Task List"));
        assert!(markdown.contains("Task 1"));
        assert!(markdown.contains("Task 2"));
        assert!(markdown.contains("**Stats:**"));
    }

    #[test]
    fn test_task_service_clear() {
        let mut task_service = TaskService::new();
        task_service.append("Task 1").unwrap();
        task_service.append("Task 2").unwrap();

        let result = task_service.clear();

        assert!(result.is_ok());
        assert!(task_service.is_empty());
        assert_eq!(task_service.len(), 0);
    }
}
