use std::path::PathBuf;

use async_trait::async_trait;
use crossterm::style::Stylize;
use derive_setters::Setters;
use forge_domain::{Command, Usage, UserInput};
use promptuity::themes::MinimalTheme;
use promptuity::{Promptuity, Term};
use tokio::fs;

use crate::autocomplete::{AutocompleteInput, MultiTriggerSuggester};
use crate::console::CONSOLE;
use crate::StatusDisplay;

/// Console implementation for handling user input via command line.
#[derive(Debug, Default, Setters)]
pub struct Console {
    commands: Vec<String>,
    files: Vec<String>,
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
        let help = help_text.map(|a| a.to_string()).unwrap_or(
            format!("[Available commands: {}]", self.commands.join(", "))
                .cyan()
                .to_string(),
        );

        // TODO: need API like: prompter.prompt(initial_text, hint, suggester);
        let mut input = AutocompleteInput::new(initial_text.unwrap_or(""))
            .with_suggester(MultiTriggerSuggester::new(
                self.files.clone(),
                self.commands.clone(),
            ))
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
