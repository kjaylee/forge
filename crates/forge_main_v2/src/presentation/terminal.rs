use std::sync::Arc;

use anyhow::Result;
use colored::Colorize;
use forge_api::API;

use super::cli::Cli;
use crate::application::{ForgeApp, UserInterface};
use crate::domain::{Command, EventBuilder, ForgeServices};
use crate::infrastructure::CONSOLE;
use crate::presentation::prompt::PromptFormatter;

pub struct ForgeTerminal<S: ForgeServices, U: UserInterface> {
    app: ForgeApp<S, U>,
    ui: Arc<U>,
    cli: Cli,
}

impl<S: ForgeServices, U: UserInterface> ForgeTerminal<S, U> {
    pub fn new(services: Arc<S>, ui: Arc<U>, cli: Cli) -> Self {
        Self { app: ForgeApp::new(services.clone(), ui.clone()), ui, cli }
    }

    pub async fn run(&mut self) -> Result<()> {
        // Handle CLI-specific flows
        if let Some(dispatch_json) = self.cli.event.clone() {
            let event: EventBuilder = serde_json::from_str(&dispatch_json)?;
            // Handle event dispatch with current mode
            let conversation_id = self.app.init_conversation(None).await?;
            let mode = self.app.state.mode.clone();
            let event = event.into_event(mode.as_ref());

            // Create chat request and process
            let chat = forge_api::ChatRequest::new(event, conversation_id.clone());
            let mut stream = self.app.services.api().chat(chat).await?;

            return self.app.process_chat_stream(&mut stream).await;
        }

        // Handle direct prompt if provided
        if let Some(prompt) = self.cli.prompt.clone() {
            return self.app.process_user_input(prompt).await;
        }

        // Interactive mode with command loop
        self.app
            .init_conversation(self.cli.workflow.as_deref().map(std::path::Path::new))
            .await?;
        self.display_banner()?;

        // Initial prompt
        let formatter = PromptFormatter::default();
        let mut input_str = self.ui.prompt_user(&formatter.to_context())?;

        // Command processing loop
        loop {
            let command = self.app.command_processor.parse_command(&input_str)?;

            match command {
                Command::Exit => break,
                _ => {
                    if let Err(e) = self.app.handle_command(command).await {
                        self.ui.display_error(&format!("Command error: {}", e))?;
                    }

                    // Update prompt context based on current state
                    let mut formatter = PromptFormatter::default();

                    if let Some(title) = &self.app.state.current_title {
                        formatter = formatter.title(title);
                    }

                    if let Some(mode) = &self.app.state.mode {
                        formatter = formatter.mode(mode.clone());
                    }

                    formatter = formatter.usage(self.app.state.usage.clone());

                    // Get next command
                    input_str = self.ui.prompt_user(&formatter.to_context())?;
                }
            }
        }

        Ok(())
    }

    fn display_banner(&self) -> Result<()> {
        // Display banner using command names from the application
        let command_names = self.app.command_processor.get_command_names();

        // Print banner with available commands
        let command_list = command_names.join(", ");
        let banner = include_str!("../infrastructure/banner");
        CONSOLE.writeln(format!("{} {}", banner.dimmed(), command_list.bold()))?;

        Ok(())
    }
}
