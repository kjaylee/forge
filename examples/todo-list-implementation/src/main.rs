use clap::{Parser, Subcommand};
use colored::*;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;
use std::process;

// Define the data structure for a task
#[derive(Debug, Serialize, Deserialize, Clone)]
struct Task {
    id: usize,
    title: String,
    completed: bool,
}

// Define the data structure for the todo list
#[derive(Debug, Serialize, Deserialize)]
struct TodoList {
    tasks: Vec<Task>,
    next_id: usize,
}

impl TodoList {
    // Create a new todo list
    fn new() -> Self {
        TodoList {
            tasks: Vec::new(),
            next_id: 1,
        }
    }

    // Add a new task
    fn add(&mut self, title: String) -> usize {
        let id = self.next_id;
        self.tasks.push(Task {
            id,
            title,
            completed: false,
        });
        self.next_id += 1;
        id
    }

    // Complete a task
    fn complete(&mut self, id: usize) -> Result<(), String> {
        if let Some(task) = self.tasks.iter_mut().find(|t| t.id == id) {
            task.completed = true;
            Ok(())
        } else {
            Err(format!("Task with ID {} not found", id))
        }
    }

    // Uncomplete a task
    fn uncomplete(&mut self, id: usize) -> Result<(), String> {
        if let Some(task) = self.tasks.iter_mut().find(|t| t.id == id) {
            task.completed = false;
            Ok(())
        } else {
            Err(format!("Task with ID {} not found", id))
        }
    }

    // Remove a task
    fn remove(&mut self, id: usize) -> Result<Task, String> {
        if let Some(position) = self.tasks.iter().position(|t| t.id == id) {
            let task = self.tasks.remove(position);
            Ok(task)
        } else {
            Err(format!("Task with ID {} not found", id))
        }
    }

    // List all tasks
    fn list(&self) -> &Vec<Task> {
        &self.tasks
    }
}

// Define the CLI commands
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Add a new task
    Add {
        /// The title of the task
        title: String,
    },
    /// List all tasks
    List,
    /// Mark a task as completed
    Complete {
        /// The ID of the task to complete
        id: usize,
    },
    /// Mark a task as not completed
    Uncomplete {
        /// The ID of the task to uncomplete
        id: usize,
    },
    /// Remove a task
    Remove {
        /// The ID of the task to remove
        id: usize,
    },
}

fn main() {
    // Parse command line arguments
    let cli = Cli::parse();

    // Get the path to the data file
    let data_path = get_data_path();

    // Load existing todo list or create a new one
    let mut todo_list = load_todo_list(&data_path).unwrap_or_else(|_| TodoList::new());

    // Process the command
    match &cli.command {
        Some(Commands::Add { title }) => {
            // Validate that the title is not empty
            if title.trim().is_empty() {
                eprintln!("{}", "Error: Task title cannot be empty".red());
                process::exit(1);
            }

            let id = todo_list.add(title.clone());
            println!("{} {}", "Task added:".green(), format!("{}. {}", id, title));
        }
        Some(Commands::List) => {
            let tasks = todo_list.list();
            if tasks.is_empty() {
                println!("{}", "No tasks found. Add one with 'todo add <title>'".yellow());
            } else {
                for task in tasks {
                    let status = if task.completed {
                        "[x]".green()
                    } else {
                        "[ ]".red()
                    };
                    println!("{}. {} {}", task.id, status, task.title);
                }
            }
        }
        Some(Commands::Complete { id }) => match todo_list.complete(*id) {
            Ok(()) => {
                let task = todo_list.tasks.iter().find(|t| t.id == *id).unwrap();
                println!("{} {}", "Task completed:".green(), format!("{}. {}", id, task.title));
            }
            Err(err) => {
                eprintln!("{} {}", "Error:".red(), err);
                process::exit(1);
            }
        },
        Some(Commands::Uncomplete { id }) => match todo_list.uncomplete(*id) {
            Ok(()) => {
                let task = todo_list.tasks.iter().find(|t| t.id == *id).unwrap();
                println!(
                    "{} {}",
                    "Task marked as not completed:".green(),
                    format!("{}. {}", id, task.title)
                );
            }
            Err(err) => {
                eprintln!("{} {}", "Error:".red(), err);
                process::exit(1);
            }
        },
        Some(Commands::Remove { id }) => match todo_list.remove(*id) {
            Ok(task) => {
                println!(
                    "{} {}",
                    "Task removed:".green(),
                    format!("{}. {}", id, task.title)
                );
            }
            Err(err) => {
                eprintln!("{} {}", "Error:".red(), err);
                process::exit(1);
            }
        },
        None => {
            // No command specified, show help
            print_help();
        }
    }

    // Save the todo list
    if let Err(err) = save_todo_list(&todo_list, &data_path) {
        eprintln!("{} {}", "Error saving todo list:".red(), err);
        process::exit(1);
    }
}

// Get the path to the data file
fn get_data_path() -> PathBuf {
    let mut path = dirs::home_dir().unwrap_or_else(|| {
        eprintln!("{}", "Error: Could not find home directory".red());
        process::exit(1);
    });
    path.push(".todo-data.json");
    path
}

// Load the todo list from the data file
fn load_todo_list(path: &PathBuf) -> Result<TodoList, String> {
    match fs::read_to_string(path) {
        Ok(data) => match serde_json::from_str(&data) {
            Ok(todo_list) => Ok(todo_list),
            Err(err) => Err(format!("Could not parse todo list data: {}", err)),
        },
        Err(_) => Err("No existing todo list found, creating a new one".to_string()),
    }
}

// Save the todo list to the data file
fn save_todo_list(todo_list: &TodoList, path: &PathBuf) -> Result<(), String> {
    match serde_json::to_string_pretty(todo_list) {
        Ok(data) => match fs::write(path, data) {
            Ok(()) => Ok(()),
            Err(err) => Err(format!("Could not write to data file: {}", err)),
        },
        Err(err) => Err(format!("Could not serialize todo list: {}", err)),
    }
}

// Print help information
fn print_help() {
    println!("{}", "TODO - A simple CLI todo list manager".yellow().bold());
    println!();
    println!("{}", "USAGE:".yellow());
    println!("  todo <COMMAND>");
    println!();
    println!("{}", "COMMANDS:".yellow());
    println!("  add <TITLE>       Add a new task");
    println!("  list              List all tasks");
    println!("  complete <ID>     Mark a task as completed");
    println!("  uncomplete <ID>   Mark a task as not completed");
    println!("  remove <ID>       Remove a task");
    println!("  help              Show this help message");
} 