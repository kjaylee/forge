use std::collections::HashMap;
use std::path::PathBuf;

use async_trait::async_trait;
use forge_api::Model;

use crate::info::Info;
use crate::ui::PartialEvent;

fn humanize_context_length(length: u64) -> String {
    if length >= 1_000_000 {
        format!("{:.1}M context", length as f64 / 1_000_000.0)
    } else if length >= 1_000 {
        format!("{:.1}K context", length as f64 / 1_000.0)
    } else {
        format!("{} context", length)
    }
}

impl From<&[Model]> for Info {
    fn from(models: &[Model]) -> Self {
        let mut info = Info::new();

        for model in models.iter() {
            if let Some(context_length) = model.context_length {
                info = info.add_key_value(&model.id, humanize_context_length(context_length));
            } else {
                info = info.add_key(&model.id);
            }
        }

        info
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForgeCommand {
    pub name: String,
    pub description: String,
}

impl From<HashMap<String, String>> for ForgeCommandManager {
    fn from(value: HashMap<String, String>) -> Self {
        ForgeCommandManager::default().register_all(value.into_iter().map(
            |(command, description)| {
                let name = if command.starts_with("/") {
                    command
                } else {
                    format!("/{}", command)
                };
                ForgeCommand { name, description }
            },
        ))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForgeCommandManager {
    commands: Vec<ForgeCommand>,
}

impl Default for ForgeCommandManager {
    fn default() -> Self {
        ForgeCommandManager { commands: vec![] }
            .register(ForgeCommand {
                name: "/new".to_string(),
                description: "Start a new conversation while preserving history.".to_string(),
            })
            .register(ForgeCommand {
                name: "/info".to_string(),
                description: "Display system environment information.".to_string(),
            })
            .register(ForgeCommand {
                name: "/exit".to_string(),
                description: "Exit the application without any further action.".to_string(),
            })
            .register(ForgeCommand {
                name: "/models".to_string(),
                description: "Lists the models available for use.".to_string(),
            })
            .register(ForgeCommand {
                name: "/act".to_string(),
                description: "Switch to \"act\" mode.".to_string(),
            })
            .register(ForgeCommand {
                name: "/plan".to_string(),
                description: "Switch to \"plan\" mode.".to_string(),
            })
            .register(ForgeCommand {
                name: "/help".to_string(),
                description: "Switch to \"help\" mode.".to_string(),
            })
            .register(ForgeCommand {
                name: "/dump".to_string(),
                description: "Dumps the current conversation into a json file".to_string(),
            })
    }
}

impl ForgeCommandManager {
    /// Registers multiple commands to the manager.
    pub fn register_all<I, T>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Into<ForgeCommand>,
    {
        self.commands.extend(iter.into_iter().map(Into::into));
        self
    }

    /// Finds a command by name.
    pub fn find(&self, command: &str) -> Option<&ForgeCommand> {
        self.commands.iter().find(|c| c.name == command)
    }

    pub fn command_names(&self) -> Vec<String> {
        self.commands
            .iter()
            .map(|command| command.name.clone())
            .collect::<Vec<_>>()
    }

    /// Registers a new command to the manager.
    pub fn register<F: Into<ForgeCommand>>(mut self, command: F) -> Self {
        self.commands.push(command.into());
        self
    }

    /// Lists all registered commands.
    pub fn list(&self) -> Vec<ForgeCommand> {
        self.commands.clone()
    }

    pub fn parse(&self, input: &str) -> anyhow::Result<Command> {
        let trimmed = input.trim();
        let is_command = trimmed.starts_with("/");
        if !is_command {
            return Ok(Command::Message(trimmed.to_string()));
        }

        match trimmed {
            "/new" => Ok(Command::New),
            "/info" => Ok(Command::Info),
            "/exit" => Ok(Command::Exit),
            "/models" => Ok(Command::Models),
            "/dump" => Ok(Command::Dump),
            "/act" => Ok(Command::Act),
            "/plan" => Ok(Command::Plan),
            "/help" => Ok(Command::Help),
            text => {
                let parts = text.split_ascii_whitespace().collect::<Vec<&str>>();

                if let Some(parsed_command) = parts.first() {
                    let args = parts
                        .get(1..)
                        .map(|args| args.join(" "))
                        .unwrap_or_default();

                    // if command is registered in our system then dispatch the event.
                    if let Some(command) = self.find(parsed_command) {
                        Ok(Command::Custom(PartialEvent::new(
                            command.name.clone().strip_prefix('/').unwrap().to_string(),
                            args,
                        )))
                    } else {
                        Err(anyhow::anyhow!("Command not registered within the system."))
                    }
                } else {
                    Err(anyhow::anyhow!("Invalid Command Format."))
                }
            }
        }
    }
}

/// Represents user input types in the chat application.
///
/// This enum encapsulates all forms of input including:
/// - System commands (starting with '/')
/// - Regular chat messages
/// - File content
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// Start a new conversation while preserving history.
    /// This can be triggered with the '/new' command.
    New,
    /// A regular text message from the user to be processed by the chat system.
    /// Any input that doesn't start with '/' is treated as a message.
    Message(String),
    /// Display system environment information.
    /// This can be triggered with the '/info' command.
    Info,
    /// Exit the application without any further action.
    Exit,
    /// Lists the models available for use.
    Models,
    /// Switch to "act" mode.
    /// This can be triggered with the '/act' command.
    Act,
    /// Switch to "plan" mode.
    /// This can be triggered with the '/plan' command.
    Plan,
    /// Switch to "help" mode.
    /// This can be triggered with the '/help' command.
    Help,
    /// Dumps the current conversation into a json file
    Dump,
    /// Handles custom command defined in workflow file.
    Custom(PartialEvent),
}

/// A trait for handling user input in the application.
///
/// This trait defines the core functionality needed for processing
/// user input, whether it comes from a command line interface,
/// GUI, or file system.
#[async_trait]
pub trait UserInput {
    type PromptInput;
    /// Read content from a file and convert it to the input type.
    ///
    /// # Arguments
    /// * `path` - The path to the file to read
    ///
    /// # Returns
    /// * `Ok(Input)` - Successfully read and parsed file content
    /// * `Err` - Failed to read or parse file
    async fn upload<P: Into<PathBuf> + Send>(&self, path: P) -> anyhow::Result<Command>;

    /// Prompts for user input with optional help text and initial value.
    ///
    /// # Arguments
    /// * `help_text` - Optional help text to display with the prompt
    /// * `initial_text` - Optional initial text to populate the input with
    ///
    /// # Returns
    /// * `Ok(Input)` - Successfully processed input
    /// * `Err` - An error occurred during input processing
    async fn prompt(&self, input: Option<Self::PromptInput>) -> anyhow::Result<Command>;
}
