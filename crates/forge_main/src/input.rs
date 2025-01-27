use std::path::PathBuf;

use async_trait::async_trait;
use colored::Colorize;
use forge_domain::{Command, Usage, UserInput};
use promptuity::themes::MinimalTheme;
use promptuity::{Promptuity, Term};
use tokio::fs;

use crate::autocomplete::{AutocompleteInput, StaticSuggester, Suggester, SuggestionContext};
use crate::console::CONSOLE;
use crate::StatusDisplay;

/// Console implementation for handling user input via command line.
#[derive(Debug, Default)]
pub struct Console;

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
        let help = help_text.map(|a| a.to_string()).unwrap_or(format!(
            "Available commands: {}",
            Command::available_commands().join(", ")
        ));

        // TODO: need API like: prompter.prompt(initial_text, hint, suggester);
        let mut input = AutocompleteInput::with_custom_suggester(
            initial_text.unwrap_or(""),
            MultiTriggerSuggester::new(vec![], Command::available_commands()),
        )
        .with_hint(help);
        let mut term = Term::default();
        let mut theme = MinimalTheme::default();
        let mut p = Promptuity::new(&mut term, &mut theme);

        loop {
            CONSOLE.writeln("")?;
            p.begin()?;
            let text = p.prompt(&mut input)?;
            p.finish()?;

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

/// A custom suggester that supports multiple trigger patterns and actions for these triggers.
/// eg. files with '@' and commands with '/'
struct MultiTriggerSuggester {
    files: StaticSuggester,
    commands: StaticSuggester,
}

impl MultiTriggerSuggester {
    fn new(files: Vec<String>, commands: Vec<String>) -> Self {
        Self {
            files: StaticSuggester::new(files)
                .with_triggers(vec!['@'])
                .with_submit_on_select(false), // Don't submit after selecting file
            commands: StaticSuggester::new(commands)
                .with_triggers(vec!['/'])
                .with_submit_on_select(true), // Submit immediately after selecting command
        }
    }
}

impl Suggester for MultiTriggerSuggester {
    fn get_suggestions(&self, input: &str, cursor_position: usize) -> SuggestionContext {
        let result = self.files.get_suggestions(input, cursor_position);
        if result.found() {
            return result;
        }
        self.commands.get_suggestions(input, cursor_position)
    }
}
