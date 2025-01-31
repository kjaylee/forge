use std::path::PathBuf;

use async_trait::async_trait;
use forge_domain::{Command, Usage, UserInput};
use tokio::fs;

use crate::console::CONSOLE;
use crate::prompting_engine::{AgentChatPrompt, ReadResult, ReedLineEngine};
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
        _initial_text: Option<&str>,
    ) -> anyhow::Result<Command> {
        CONSOLE.writeln("")?;
        let mut engine = ReedLineEngine::start();
        let prompt = AgentChatPrompt::default().start(help_text.map(|t| t.to_owned()));
        loop {
            let result = engine.prompt(&prompt)?;
            match result {
                ReadResult::Continue => continue,
                ReadResult::Exit => return Ok(Command::Exit),
                ReadResult::Success(text) => match Command::parse(&text) {
                    Ok(input) => return Ok(input),
                    Err(e) => {
                        CONSOLE.writeln(
                            StatusDisplay::failed(e.to_string(), Usage::default()).format(),
                        )?;
                    }
                },
            }
        }
    }
}