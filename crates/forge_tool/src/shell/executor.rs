use std::path::PathBuf;

use tokio::process::Command;

use super::streamer::CommandStreamer;

/// A command executor that handles command creation and execution
#[derive(Debug)]
pub struct CommandExecutor {
    command: Command,
}

impl CommandExecutor {
    /// Create a new command executor with the specified command and working directory
    pub fn new(command: &str) -> Self {
        let command = if cfg!(target_os = "windows") {
            let mut c = Command::new("cmd");
            c.args(["/C", command]);
            c
        } else {
            let mut c = Command::new("sh");
            c.args(["-c", command]);
            c
        };
        Self { command }
    }

    // Set the current working directory for the command
    pub fn with_cwd(mut self, cwd: PathBuf) -> Self {
        self.command.current_dir(&cwd);
        self
    }

    /// pipes the i/o
    pub fn piped(mut self) -> Self {
        self.command
            .env("CLICOLOR_FORCE", "1")
            .stdin(std::process::Stdio::inherit())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());

        self
    }

    // forks command and attaches it to streamer.
    pub fn execute(mut self) -> anyhow::Result<CommandStreamer> {
        let child = self.command.spawn()?;
        Ok(CommandStreamer::new(child))
    }
}
