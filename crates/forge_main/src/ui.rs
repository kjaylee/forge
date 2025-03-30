use std::sync::Arc;

use anyhow::Result;
use colored::Colorize;
use forge_api::{AgentMessage, ChatRequest, ChatResponse, ConversationId, Event, Model, API};
use forge_display::TitleFormat;
use lazy_static::lazy_static;
use serde::Deserialize;
use serde_json::Value;
use tokio_stream::StreamExt;
use tracing::error;

use crate::banner;
use crate::cli::Cli;
use crate::console::CONSOLE;
use crate::info::Info;
use crate::input::Console;
use crate::model::{Command, ForgeCommandManager, UserInput};
use crate::state::{Mode, UIState};

// Event type constants moved to UI layer
// Event names will be prefixed with the current mode (act/, plan/, or help/)
// during dispatch For example: "act/user/task_init", "plan/user/task_update",
// "help/user/task_init", etc.
pub const EVENT_USER_TASK_INIT: &str = "task_init";
pub const EVENT_USER_TASK_UPDATE: &str = "task_update";
pub const EVENT_TITLE: &str = "ui/title";

lazy_static! {
    pub static ref TRACKER: forge_tracker::Tracker = forge_tracker::Tracker::default();
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, Default)]
pub struct PartialEvent {
    pub name: String,
    pub value: Value,
}

impl PartialEvent {
    pub fn new<V: Into<Value>>(name: impl ToString, value: V) -> Self {
        Self { name: name.to_string(), value: value.into() }
    }

    pub fn into_event(self) -> Event {
        Event::new(vec![self.name], self.value)
    }
}

impl From<PartialEvent> for Event {
    fn from(value: PartialEvent) -> Self {
        value.into_event()
    }
}

pub struct UI<F> {
    state: UIState,
    api: Arc<F>,
    console: Console,
    command: Arc<ForgeCommandManager>,
    cli: Cli,
    models: Option<Vec<Model>>,
    #[allow(dead_code)] // The guard is kept alive by being held in the struct
    _guard: forge_tracker::Guard,
}

impl<F: API> UI<F> {
    // Set the current mode and update conversation variable
    async fn handle_mode_change(&mut self, mode: Mode) -> Result<()> {
        // Update the mode in state
        self.state.mode = Some(mode);

        // Show message that mode changed
        let mode_str = self.state.get_mode()?.to_string();

        // Set the mode variable in the conversation if a conversation exists
        let conversation_id = self.init_conversation().await?;
        self.api
            .set_variable(
                &conversation_id,
                "mode".to_string(),
                Value::from(mode_str.as_str()),
            )
            .await?;

        // Try to get the mode description from the configuration
        let mut description = String::from("custom mode");
        if let Ok(Some(conversation)) = self.api.conversation(&conversation_id).await {
            if let Some(mode_config) = conversation.workflow.find_mode(mode_str.as_str()) {
                description = format!("{} {}", "MODE".bold(), mode_config.description);
            }
        }

        CONSOLE.write(
            TitleFormat::success(&mode_str)
                .sub_title(&description)
                .format(),
        )?;

        Ok(())
    }

    // Helper method to create events with mode prefix
    fn create_user_event(&mut self, content: impl Into<Value>) -> Result<Event> {
        let mode = self.state.get_mode()?.to_string().to_lowercase();
        let author = "user".to_string();

        let name = if self.state.is_first {
            self.state.is_first = false;
            EVENT_USER_TASK_INIT
        } else {
            EVENT_USER_TASK_UPDATE
        };

        Ok(Event::new(
            vec![mode.as_str(), author.as_str(), name],
            content,
        ))
    }

    pub fn init(cli: Cli, api: Arc<F>) -> Result<Self> {
        // Parse CLI arguments first to get flags
        let env = api.environment();
        let command = Arc::new(ForgeCommandManager::default());
        Ok(Self {
            state: Default::default(),
            api,
            console: Console::new(env.clone(), command.clone()),
            cli,
            command,
            models: None,
            _guard: forge_tracker::init_tracing(env.log_path())?,
        })
    }

    pub async fn run(&mut self) -> Result<()> {
        // Check for dispatch flag first
        if let Some(dispatch_json) = self.cli.event.clone() {
            let event: PartialEvent = serde_json::from_str(&dispatch_json)?;
            return self.chat(event.into()).await;
        }

        // Handle direct prompt if provided
        let prompt = self.cli.prompt.clone();
        if let Some(prompt) = prompt {
            let event = self.create_user_event(prompt)?;
            self.chat(event).await?;
            return Ok(());
        }

        // Display the banner in dimmed colors since we're in interactive mode
        self.init_conversation().await?;
        banner::display(self.command.command_names())?;

        // Get initial input from file or prompt
        let mut input = match &self.cli.command {
            Some(path) => self.console.upload(path).await?,
            None => self.console.prompt(None).await?,
        };

        loop {
            match input {
                Command::Dump => {
                    self.handle_dump().await?;
                    let prompt_input = Some((&self.state).into());
                    input = self.console.prompt(prompt_input).await?;
                    continue;
                }
                Command::New => {
                    self.state = Default::default();
                    self.init_conversation().await?;
                    banner::display(self.command.command_names())?;
                    input = self.console.prompt(None).await?;

                    continue;
                }
                Command::Info => {
                    let info =
                        Info::from(&self.api.environment()).extend(Info::from(&self.state.usage));

                    CONSOLE.writeln(info.to_string())?;

                    let prompt_input = Some((&self.state).into());
                    input = self.console.prompt(prompt_input).await?;
                    continue;
                }
                Command::Message(ref content) => {
                    let content_clone = content.clone();
                    let event = self.create_user_event(content_clone)?;
                    let chat_result = self.chat(event).await;
                    if let Err(err) = chat_result {
                        tokio::spawn(
                            TRACKER.dispatch(forge_tracker::EventKind::Error(format!("{:?}", err))),
                        );
                        error!(error = ?err, "Chat request failed");

                        CONSOLE.writeln(TitleFormat::failed(format!("{:?}", err)).format())?;
                    }
                    let prompt_input = Some((&self.state).into());
                    input = self.console.prompt(prompt_input).await?;
                }
                Command::Exit => {
                    break;
                }
                Command::Models => {
                    let models = if let Some(models) = self.models.as_ref() {
                        models
                    } else {
                        let models = self.api.models().await?;
                        self.models = Some(models);
                        self.models.as_ref().unwrap()
                    };
                    let info: Info = models.as_slice().into();
                    CONSOLE.writeln(info.to_string())?;

                    input = self.console.prompt(None).await?;
                }
                Command::Custom(event) => {
                    // Check if this is a mode command
                    if event.name == "mode" {
                        // Handle custom mode switching
                        self.handle_mode_change(Mode::new(event.value.clone()))
                            .await?;

                        let prompt_input = Some((&self.state).into());
                        input = self.console.prompt(prompt_input).await?;
                        continue;
                    }

                    if let Err(e) = self.chat(event.into()).await {
                        CONSOLE.writeln(
                            TitleFormat::failed("Failed to execute the command.")
                                .sub_title("Command Execution")
                                .error(e.to_string())
                                .format(),
                        )?;
                    }

                    input = self.console.prompt(None).await?;
                }
            }
        }

        Ok(())
    }

    async fn init_conversation(&mut self) -> Result<ConversationId> {
        match self.state.conversation_id {
            Some(ref id) => Ok(id.clone()),
            None => {
                let workflow = self.api.load(self.cli.workflow.as_deref()).await?;
                self.command.register_all(&workflow);
                let conversation_id = self.api.init(workflow.clone()).await?;
                self.state.conversation_id = Some(conversation_id.clone());

                // Set the mode from the first available mode in the configuration
                if let Some(first_mode) = workflow.modes.first() {
                    self.state.mode = Some(Mode::new(&first_mode.name));
                    // Set the mode variable
                    self.api
                        .set_variable(
                            &conversation_id,
                            "mode".to_string(),
                            Value::from(self.state.get_mode()?.to_string()),
                        )
                        .await?;
                } else {
                    return Err(anyhow::anyhow!("No modes defined in workflow configuration. At least one mode must be configured."));
                }

                Ok(conversation_id)
            }
        }
    }

    async fn handle_chat_stream(
        &mut self,
        stream: &mut (impl StreamExt<Item = Result<AgentMessage<ChatResponse>>> + Unpin),
    ) -> Result<()> {
        loop {
            tokio::select! {
                _ = tokio::signal::ctrl_c() => {
                    return Ok(());
                }
                maybe_message = stream.next() => {
                    match maybe_message {
                        Some(Ok(message)) => self.handle_chat_response(message)?,
                        Some(Err(err)) => {
                            return Err(err);
                        }
                        None => return Ok(()),
                    }
                }
            }
        }
    }

    async fn handle_dump(&mut self) -> Result<()> {
        if let Some(conversation_id) = self.state.conversation_id.clone() {
            let conversation = self.api.conversation(&conversation_id).await?;
            if let Some(conversation) = conversation {
                let timestamp = chrono::Local::now().format("%Y-%m-%d_%H-%M-%S_%z");
                let path = self
                    .state
                    .current_title
                    .as_ref()
                    .map_or(format!("{timestamp}"), |title| {
                        format!("{timestamp}-{title}")
                    });

                let path = format!("{path}-dump.json");

                let content = serde_json::to_string_pretty(&conversation)?;
                tokio::fs::write(path.as_str(), content).await?;

                CONSOLE.writeln(
                    TitleFormat::success("dump")
                        .sub_title(format!("path: {path}"))
                        .format(),
                )?;
            } else {
                CONSOLE.writeln(
                    TitleFormat::failed("dump")
                        .error("conversation not found")
                        .sub_title(format!("conversation_id: {conversation_id}"))
                        .format(),
                )?;
            }
        }
        Ok(())
    }

    fn handle_chat_response(&mut self, message: AgentMessage<ChatResponse>) -> Result<()> {
        match message.message {
            ChatResponse::Text(text) => CONSOLE.write(text.dimmed().to_string())?,
            ChatResponse::ToolCallStart(_) => {
                CONSOLE.newline()?;
                CONSOLE.newline()?;
            }
            ChatResponse::ToolCallEnd(tool_result) => {
                if !self.cli.verbose {
                    return Ok(());
                }

                let tool_name = tool_result.name.as_str();

                CONSOLE.writeln(format!("{}", tool_result.content.dimmed()))?;

                if tool_result.is_error {
                    CONSOLE.writeln(TitleFormat::failed(tool_name).format())?;
                } else {
                    CONSOLE.writeln(TitleFormat::success(tool_name).format())?;
                }
            }
            ChatResponse::Event(event) => {
                if event.name.to_string() == EVENT_TITLE {
                    self.state.current_title =
                        Some(event.value.as_str().unwrap_or_default().to_string());
                }
            }
            ChatResponse::Usage(u) => {
                self.state.usage = u;
            }
        }
        Ok(())
    }

    async fn chat(&mut self, event: Event) -> Result<()> {
        let conversation_id = self.init_conversation().await?;
        let chat = ChatRequest::new(event, conversation_id);
        let mut stream = self.api.chat(chat).await?;
        self.handle_chat_stream(&mut stream).await
    }
}
#[cfg(test)]
mod tests {
    use forge_api::ModeConfig;

    use super::*;

    #[tokio::test]
    async fn test_default_mode_from_configuration() {
        // Create a basic workflow with modes
        let workflow = forge_api::Workflow {
            modes: vec![
                ModeConfig {
                    name: "TEST_MODE".to_string(),
                    description: "The test mode".to_string(),
                    command: "/test-mode".to_string(),
                },
                ModeConfig {
                    name: "SECONDARY_MODE".to_string(),
                    description: "The secondary mode".to_string(),
                    command: "/secondary".to_string(),
                },
            ],
            ..Default::default()
        };

        // Create a UI with default state
        let mut state = UIState::default();
        assert_eq!(state.mode, None);

        // Mock setting first mode from configuration
        if let Some(first_mode) = workflow.modes.first() {
            state.mode = Some(Mode::new(&first_mode.name));
        }

        // Verify the first mode was set
        assert_eq!(state.mode.as_ref().unwrap().as_str(), "TEST_MODE");
    }
}
