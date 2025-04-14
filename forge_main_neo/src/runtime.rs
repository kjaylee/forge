use std::sync::Arc;

use anyhow::{Context, Result};
use futures::StreamExt;
use ratatui::DefaultTerminal;
use tokio::sync::mpsc;

use crate::{App, CommandExecutor, CommandList, Message};

pub struct Runtime<CommandExecutor> {
    tx: mpsc::Sender<Message>,
    rx: mpsc::Receiver<Message>,
    executor: Arc<CommandExecutor>,
}

impl<C: CommandExecutor> Runtime<C> {
    pub fn new(executor: Arc<C>) -> Self {
        // Set up a channel for chat messages with a buffer of 1000 messages
        let (tx, rx) = mpsc::channel::<Message>(1000);
        Self { tx, rx, executor }
    }

    pub async fn run(&mut self, mut terminal: DefaultTerminal, mut app: App) -> Result<()> {
        // Start polling for crossterm events
        let crossterm_tx = self.tx.clone();
        tokio::spawn(async {
            if let Err(e) = poll_crossterm_event(crossterm_tx).await {
                tracing::error!("Error polling crossterm events: {:?}", e);
            }
        });

        let mut exit = false;
        while !exit {
            terminal.draw(|frame| frame.render_widget(&mut app, frame.area()))?;
            if let Some(message) = self.rx.recv().await {
                let mut commands = CommandList::default();
                app.run(&mut commands, message).context("app loop failed")?;

                for command in commands.into_inner() {
                    if self.executor.is_exit(&command) {
                        exit = true;
                        break;
                    } else {
                        self.executor.execute(command, self.tx.clone()).await?;
                    }
                }
            } else {
                exit = true;
            }
        }

        Ok(())
    }

    pub fn sender(&self) -> mpsc::Sender<Message> {
        self.tx.clone()
    }
}

async fn poll_crossterm_event(tx: mpsc::Sender<Message>) -> Result<()> {
    let mut events = crossterm::event::EventStream::new();
    while let Some(event) = events.next().await {
        tx.send(event?.into()).await?;
    }
    Ok(())
}
