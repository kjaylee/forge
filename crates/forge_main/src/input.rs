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
#[derive(Clone, Debug)]
struct Completer {
    commands: Vec<String>,
    files: Vec<String>,
}

/// Console implementation for handling user input via command line.
#[derive(Debug)]
pub struct Console {
    commands: Vec<String>,
    files: Vec<String>,
}

impl Console {
    pub fn new(files: Vec<String>, commands: Vec<String>) -> Self {
        Self { commands, files }
    }
}

impl From<&Console> for Completer {
    fn from(console: &Console) -> Self {
        Completer {
            commands: console.commands.clone(),
            files: console.files.clone(),
        }
    }
}

impl Completer {
    fn find_last_trigger_position(input: &str) -> (&str, char) {
        if let Some(pos) = input.rfind('@').or_else(|| input.rfind('/')) {
            let trigger_char = input.chars().nth(pos).unwrap();
            let suggestion = &input[pos + 1..];
            (suggestion, trigger_char)
        } else {
            // Return an empty suggestion and a default trigger character if none found
            ("", ' ') // or any other default character
        }
    }
}

impl Completion for Completer {
    fn get(&self, input: &str) -> Option<String> {
        self.commands
            .iter()
            .find(|cmd| cmd.starts_with(input))
            .cloned()
    }

    fn get_suggestions(&self, input: &str) -> Vec<String> {
        let (suggestion, trigger_char) = Completer::find_last_trigger_position(input);
        let result = match trigger_char {
            '/' => self
                .commands
                .iter()
                .filter(|cmd| cmd.starts_with(suggestion))
                .cloned()
                .collect(),
            '@' => self
                .files
                .iter()
                .filter(|file| {
                    let file_name = file.split('/').last().unwrap_or(file);
                    file_name.contains(suggestion)
                })
                .take(5)
                .cloned()
                .collect(),
            _ => vec![],
        };

        result
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
        let completion = Completer::from(self);
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
