use forge_domain::{Status, TaskList, TaskStats};

pub fn to_markdown(task_list: &TaskList) -> String {
    if task_list.tasks().is_empty() {
        return "No tasks in the list.".to_string();
    }

    let mut markdown = String::new();

    // Calculate the width needed for padding based on the highest task ID
    let max_id_width = task_list
        .tasks()
        .iter()
        .map(|task| task.id.to_string().len())
        .max()
        .unwrap_or(1);

    for task in task_list.tasks() {
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

    let stats = TaskStats::from(task_list);
    markdown.push_str(&format!(
        "\n**Stats:** {} total, {} done, {} in progress, {} pending\n",
        stats.total_tasks, stats.done_tasks, stats.in_progress_tasks, stats.pending_tasks
    ));

    markdown
}

#[cfg(test)]
mod tests {
    use forge_domain::TaskList;
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_to_markdown_empty_task_list() {
        let fixture = TaskList::new();
        let actual = to_markdown(&fixture);
        let expected = "No tasks in the list.";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_to_markdown_single_pending_task() {
        let mut fixture = TaskList::new();
        fixture.append("Write documentation");
        let actual = to_markdown(&fixture);
        assert!(actual.contains("1. Write documentation"));
        assert!(actual.contains("**Stats:**"));
    }

    #[test]
    fn test_to_markdown_mixed_status_tasks() {
        let mut fixture = TaskList::new();
        let _task1 = fixture.append("First task");
        let task2 = fixture.append("Second task");
        fixture.append("Third task");

        // Mark second task as done
        fixture.mark_done(task2.id);

        // Mark first task as in progress manually
        fixture.get_task_mut(0).unwrap().mark_in_progress();

        let actual = to_markdown(&fixture);
        assert!(actual.contains("**First task**")); // in progress
        assert!(actual.contains("~~Second task~~")); // done
        assert!(actual.contains("3. Third task")); // pending
    }

    // Snapshot tests for markdown output
    #[test]
    fn test_empty_task_list_markdown_snapshot() {
        let fixture = TaskList::new();
        let actual = to_markdown(&fixture);
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn test_single_pending_task_markdown_snapshot() {
        let mut fixture = TaskList::new();
        fixture.append("Write documentation");
        let actual = to_markdown(&fixture);
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
        fixture.get_task_mut(0).unwrap().mark_in_progress();

        let actual = to_markdown(&fixture);
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

        let actual = to_markdown(&fixture);
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
        fixture.get_task_mut(0).unwrap().mark_in_progress(); // "Review pull request #123"
        fixture.get_task_mut(4).unwrap().mark_in_progress(); // "Refactor user service"

        let actual = to_markdown(&fixture);
        insta::assert_snapshot!(actual);
    }
}
