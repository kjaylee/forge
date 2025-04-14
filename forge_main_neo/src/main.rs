use std::{sync::mpsc, thread};

use anyhow::{Context, Result};
use forge_main_neo::{App, Message};

fn main() -> Result<()> {
    let mut terminal = ratatui::init();

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::EnableMouseCapture
    )?;

    // Set up a channel for chat messages
    let (tx, rx) = mpsc::channel::<Message>();

    let mut app = App::new();

    thread::spawn(move || poll_crossterm_event(tx).unwrap());

    let app_result = app.run(&mut terminal, rx).context("app loop failed");

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::DisableMouseCapture
    )?;

    ratatui::restore();

    app_result
}

fn poll_crossterm_event(tx: mpsc::Sender<Message>) -> Result<()> {
    loop {
        let event = ratatui::crossterm::event::read()?;
        tx.send(event.into())?;
    }
}
