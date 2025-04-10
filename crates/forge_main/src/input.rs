use std::path::PathBuf;
use std::sync::Arc;

use async_trait::async_trait;
use forge_api::Usage;
use forge_display::TitleFormat;
use forge_domain::{Conversation, ConversationId, Workflow};
use tokio::fs;

use crate::console::CONSOLE;
use crate::editor::{ForgeEditor, ReadResult};
use crate::model::{Command, ForgeCommandManager, UserInput};
use crate::prompt::ForgePrompt;
use crate::state::Mode;

/// Console implementation for handling user input via command line.
#[derive(Debug)]
pub struct Console {
    command: Arc<ForgeCommandManager>,
}

impl Console {
    /// Creates a new instance of `Console`.
    pub fn new(command: Arc<ForgeCommandManager>) -> Self {
        Self { command }
    }

    /// Create a test conversation for the editor
    fn create_temp_conversation(&self) -> Conversation {
        let id = ConversationId::generate();
        let workflow = Workflow::default();
        // Use current directory for the conversation
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("/tmp"));
        Conversation::new(id, workflow, cwd)
    }
}

#[async_trait]
impl UserInput for Console {
    type PromptInput = PromptInput;
    async fn upload<P: Into<PathBuf> + Send>(&self, path: P) -> anyhow::Result<Command> {
        let path = path.into();
        let content = fs::read_to_string(&path).await?.trim().to_string();

        CONSOLE.writeln(content.clone())?;
        Ok(Command::Message(content))
    }

    async fn prompt(&self, input: Option<Self::PromptInput>) -> anyhow::Result<Command> {
        CONSOLE.writeln("")?;

        // Create a temporary conversation for the editor
        let temp_conversation = self.create_temp_conversation();

        let mut engine = ForgeEditor::new(&temp_conversation, self.command.clone());
        let prompt: ForgePrompt = input.map(Into::into).unwrap_or_default();

        loop {
            let result = engine.prompt(&prompt)?;
            match result {
                ReadResult::Continue => continue,
                ReadResult::Exit => return Ok(Command::Exit),
                ReadResult::Empty => continue,
                ReadResult::Success(text) => {
                    tokio::spawn(
                        crate::ui::TRACKER.dispatch(forge_tracker::EventKind::Prompt(text.clone())),
                    );
                    match self.command.parse(&text) {
                        Ok(command) => return Ok(command),
                        Err(e) => {
                            CONSOLE.writeln(
                                TitleFormat::failed("command")
                                    .sub_title(e.to_string())
                                    .format(),
                            )?;
                        }
                    }
                }
            }
        }
    }
}

pub enum PromptInput {
    Update {
        title: Option<String>,
        usage: Option<Usage>,
        mode: Mode,
    },
}

impl From<PromptInput> for ForgePrompt {
    fn from(input: PromptInput) -> Self {
        match input {
            PromptInput::Update { title, usage, mode } => {
                let mut prompt = ForgePrompt::default();
                prompt.mode(mode);
                if let Some(title) = title {
                    prompt.title(title);
                }
                if let Some(usage) = usage {
                    prompt.usage(usage);
                }
                prompt
            }
        }
    }
}
