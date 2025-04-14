use anyhow::{Context, Result};
use futures::StreamExt;
use ratatui::DefaultTerminal;
use tokio::sync::mpsc;
use tracing::{debug, field::debug};

use crate::{App, Command, CommandList, Message};

pub struct Runtime;

impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}

impl Runtime {
    pub fn new() -> Self {
        Self {}
    }

    pub async fn run(&self, mut terminal: DefaultTerminal, mut app: App) -> Result<()> {
        // Set up a channel for chat messages
        let (tx, mut rx) = mpsc::channel::<Message>(1000);

        // Start polling for crossterm events
        tokio::spawn(poll_crossterm_event(tx));

        let mut exit = false;
        while !exit {
            terminal.draw(|frame| frame.render_widget(&mut app, frame.area()))?;
            if let Some(message) = rx.recv().await {
                let mut commands = CommandList::default();
                app.run(&mut commands, message).context("app loop failed")?;

                execute_command(&mut exit, commands);
            } else {
                exit = true;
            }
        }

        Ok(())
    }
}

fn execute_command(exit: &mut bool, commands: CommandList) {
    for command in commands.into_inner() {
        debug!(command = ?command, "Dispatching command");
        match command {
            Command::Suspend => {}
            Command::ToggleMode(_) => {}
            Command::UserMessage(_) => {}
            Command::Exit => {
                *exit = true;
            }
            Command::Empty => {}
        }
    }
}

async fn poll_crossterm_event(tx: mpsc::Sender<Message>) -> Result<()> {
    let mut events = crossterm::event::EventStream::new();
    while let Some(event) = events.next().await {
        tx.send(event?.into()).await?;
    }
    Ok(())
}
