use std::sync::Arc;
use std::time::Duration;

use forge_api::ForgeAPI;
use ratatui::DefaultTerminal;

use crate::event_reader::EventReader;
use crate::executor::Executor;
use crate::model::{Action, Command, State};
use crate::widgets::App;

pub async fn run(mut terminal: DefaultTerminal) -> anyhow::Result<()> {
    // Initialize channels
    let (action_tx, mut action_rx) = tokio::sync::mpsc::channel::<anyhow::Result<Action>>(1024);
    let (cmd_tx, cmd_rx) = tokio::sync::mpsc::channel::<Command>(1024);

    let mut state = State::default();
    let mut app = App::default();
    let api = ForgeAPI::init(false);

    // Initialize Executor
    let executor = Executor::new(Arc::new(api));
    executor.init(action_tx.clone(), cmd_rx).await;

    // Initial STDIN
    let event_reader = EventReader::new(Duration::from_millis(100));
    event_reader.init(action_tx.clone()).await;
    loop {
        terminal.draw(|frame| {
            frame.render_stateful_widget(&app, frame.area(), &mut state);
        })?;

        if let Some(action) = action_rx.recv().await {
            let cmd = app.update(action?, &mut state);
            if cmd == Command::Exit {
                break;
            } else {
                cmd_tx.send(cmd).await?;
            }
        } else {
            break;
        }
    }

    Ok(())
}
