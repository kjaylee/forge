use tokio::sync::mpsc;

use anyhow::Context;
use forge_main_neo::{App, Message};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut terminal = ratatui::init();

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::EnableMouseCapture
    )?;

    let (tx, rx) = tokio::sync::mpsc::channel(100);
    let mut app = App::new(rx);
    let join = tokio::spawn(poll_crossterm_event(tx));
    let app_result = app.run(&mut terminal).await.context("app loop failed");

    join.abort();
    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::DisableMouseCapture
    )?;

    ratatui::restore();

    app_result
}

async fn poll_crossterm_event(tx: mpsc::Sender<Message>) -> anyhow::Result<()> {
    loop {
        let event = ratatui::crossterm::event::read()?;
        tx.send(event.into()).await.context("send event failed")?;
    }
}
