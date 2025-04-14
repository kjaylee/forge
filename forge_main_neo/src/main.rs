use std::sync::mpsc;
use std::thread;

use anyhow::{Context, Result};
use forge_main_neo::{App, Command, CommandList, Message};

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

    let mut message = Message::Initialize;
    while !app.state.exit {
        terminal.draw(|frame| frame.render_widget(&mut app, frame.area()))?;
        message = rx.recv()?;
        let mut commands = CommandList::default();
        app.run(&mut commands, message).context("app loop failed")?;

        for command in commands.into_inner() {
            match command {
                Command::Suspend => {}
                Command::ToggleMode(_) => {}
                Command::UserMessage(_) => {}
                Command::Empty => {}
            }
        }
    }

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::DisableMouseCapture
    )?;

    ratatui::restore();

    Ok(())
}

fn poll_crossterm_event(tx: mpsc::Sender<Message>) -> Result<()> {
    loop {
        let event = ratatui::crossterm::event::read()?;
        tx.send(event.into())?;
    }
}
