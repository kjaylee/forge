use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use forge_api::{Model, Workflow};
use strum::{EnumProperty, IntoEnumIterator};
use strum_macros::{EnumIter, EnumProperty};

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

impl From<&Workflow> for ForgeCommandManager {
    fn from(value: &Workflow) -> Self {
        let cmd = ForgeCommandManager::default();
        cmd.register_all(value);
        cmd
    }
}

#[derive(Debug)]
pub struct ForgeCommandManager {
    commands: Arc<Mutex<Vec<ForgeCommand>>>,
}

impl Default for ForgeCommandManager {
    fn default() -> Self {
        let commands = Command::iter()
            .filter(|command| !matches!(command, Command::Message(_)))
            .filter(|command| !matches!(command, Command::Custom(_)))
            .map(|command| ForgeCommand {
                name: command.name().to_string(),
                description: command.usage().to_string(),
            })
            .collect::<Vec<_>>();

        ForgeCommandManager { commands: Arc::new(Mutex::new(commands)) }
    }
}

impl ForgeCommandManager {
    /// Registers multiple commands to the manager.
    pub fn register_all(&self, workflow: &Workflow) {
        self.commands.lock().unwrap().extend(
            workflow
                .commands
                .clone()
                .into_iter()
                .map(|(name, description)| ForgeCommand {
                    name: format!("/{}", name),
                    description,
                }),
        );
    }

    /// Finds a command by name.
    fn find(&self, command: &str) -> Option<ForgeCommand> {
        self.commands
            .lock()
            .unwrap()
            .iter()
            .find(|c| c.name == command)
            .cloned()
    }

    pub fn command_names(&self) -> Vec<String> {
        self.commands
            .lock()
            .unwrap()
            .iter()
            .map(|command| command.name.clone())
            .collect::<Vec<_>>()
    }

    /// Lists all registered commands.
    pub fn list(&self) -> Vec<ForgeCommand> {
        self.commands.lock().unwrap().clone()
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
#[derive(Debug, Clone, PartialEq, Eq, EnumProperty, EnumIter)]
pub enum Command {
    /// Start a new conversation while preserving history.
    /// This can be triggered with the '/new' command.
    #[strum(props(usage = "Start a new conversation while preserving history."))]
    New,
    /// A regular text message from the user to be processed by the chat system.
    /// Any input that doesn't start with '/' is treated as a message.
    #[strum(props(
        usage = "A regular text message from the user to be processed by the chat system."
    ))]
    Message(String),
    /// Display system environment information.
    /// This can be triggered with the '/info' command.
    #[strum(props(usage = "Display system environment information."))]
    Info,
    /// Exit the application without any further action.
    #[strum(props(usage = "Exit the application without any further action."))]
    Exit,
    /// Lists the models available for use.
    #[strum(props(usage = "Lists the models available for use."))]
    Models,
    /// Switch to "act" mode.
    /// This can be triggered with the '/act' command.
    #[strum(props(usage = "Switch to \"act\" mode."))]
    Act,
    /// Switch to "plan" mode.
    /// This can be triggered with the '/plan' command.
    #[strum(props(usage = "Switch to \"plan\" mode."))]
    Plan,
    /// Switch to "help" mode.
    /// This can be triggered with the '/help' command.
    #[strum(props(usage = "Switch to \"help\" mode."))]
    Help,
    /// Dumps the current conversation into a json file
    #[strum(props(usage = "Dumps the current conversation into a json file"))]
    Dump,
    /// Handles custom command defined in workflow file.
    #[strum(props(usage = "Custom command defined in workflow file."))]
    Custom(PartialEvent),
}

impl Command {
    pub fn name(&self) -> &str {
        match self {
            Command::New => "/new",
            Command::Message(_) => "/message",
            Command::Info => "/info",
            Command::Exit => "/exit",
            Command::Models => "/models",
            Command::Act => "/act",
            Command::Plan => "/plan",
            Command::Help => "/help",
            Command::Dump => "/dump",
            Command::Custom(event) => &event.name,
        }
    }

    /// Returns the usage description for the command.
    pub fn usage(&self) -> &str {
        self.get_str("usage").unwrap()
    }
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
