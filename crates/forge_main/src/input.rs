use std::path::PathBuf;

use async_trait::async_trait;
use colored::Colorize;
use dialoguer::theme::ColorfulTheme;
use dialoguer::{Completion, Input};
use forge_domain::{Command, Usage, UserInput};
use tokio::fs;

use crate::console::CONSOLE;
use crate::StatusDisplay;

/// Provides command autocompletion functionality for the input prompt.
///
/// This struct maintains a list of available commands and implements
/// the Autocomplete trait to provide suggestions as the user types.
#[derive(Clone)]
struct CommandCompleter {
    commands: Vec<String>,
}

/// Console implementation for handling user input via command line.
#[derive(Debug, Default)]
pub struct Console;

impl CommandCompleter {
    /// Creates a new command completer with the list of available commands
    fn new() -> Self {
        Self { commands: Command::available_commands() }
    }
}

impl Completion for CommandCompleter {
    fn get(&self, input: &str) -> Option<String> {
        self.commands
            .iter()
            .find(|cmd| cmd.starts_with(input))
            .cloned()
    }
}

#[async_trait]
impl UserInput for Console {
    async fn upload<P: Into<PathBuf> + Send>(&self, path: P) -> anyhow::Result<Command> {
        let path = path.into();
        let content = fs::read_to_string(&path).await?.trim().to_string();
        CONSOLE.writeln(content.clone())?;
        Ok(Command::Message(content))
    }

    async fn prompt(
        &self,
        help_text: Option<&str>,
        initial_text: Option<&str>,
    ) -> anyhow::Result<Command> {
        let theme = ColorfulTheme::default();
        let completion = CommandCompleter::new();
        let help = help_text.map(|a| a.bright_white().to_string()).unwrap_or({
            let commands = Command::available_commands().join(", ");
            format!("[Available commands: {}]", commands)
                .bright_cyan()
                .to_string()
        });
        loop {
            CONSOLE.writeln("")?;
            CONSOLE.writeln(&help)?;

            let input = Input::<String>::with_theme(&theme)
                .with_prompt("")
                .completion_with(&completion)
                .with_initial_text(initial_text.unwrap_or(""));

            let text = input.interact_text()?;
            match Command::parse(&text) {
                Ok(input) => return Ok(input),
                Err(e) => {
                    CONSOLE
                        .writeln(StatusDisplay::failed(e.to_string(), Usage::default()).format())?;
                }
            }
        }
    }
}
