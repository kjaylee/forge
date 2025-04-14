use tokio::sync::mpsc;

use crate::{Command, CommandExecutor, Message};

pub struct ForgeCommandExecutor {}

impl Default for ForgeCommandExecutor {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeCommandExecutor {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl CommandExecutor for ForgeCommandExecutor {
    async fn execute(&self, command: Command, tx: mpsc::Sender<Message>) -> anyhow::Result<()> {
        Ok(())
    }

    fn is_exit(&self, command: &Command) -> bool {
        matches!(command, Command::Exit)
    }
}
