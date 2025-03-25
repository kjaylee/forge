Product Requirements Document: Todo List CLI Application - Mark Task as Done

Overview
This document outlines the requirements for marking tasks as done in a simple command-line Todo List application built with Rust.

Goal
Enable users to mark todo items as completed through a command-line interface

Functional Requirements
Task Completion (P0)

1.1. Users must be able to mark existing tasks as done using their ID
1.2. The system should provide a command done to mark tasks as completed
1.3. The system must validate that the specified task ID exists
1.4. Tasks should maintain a completion status (done/not done)
1.5. The system should confirm task completion with a success message
1.6. The system should display an error if the specified task ID doesn't exist
1.7. The system should prevent marking an already completed task as done

Implementation Examples
```bash
# Marking a task as done
$ todo done 1
Task marked as done: 1. Buy groceries

# Attempting to mark non-existent task
$ todo done 999
Error: Task with ID 999 not found

# Attempting to mark already completed task
$ todo done 1
Error: Task 1 is already marked as done
``` 