use std::sync::Arc;
use std::time::Duration;

use forge_api::ForgeAPI;
use ratatui::DefaultTerminal;
use ratatui::widgets::Widget;

use crate::action::Action;
use crate::command::Command;
use crate::event_reader::EventReader;
use crate::executor::Executor;
use crate::widgets::App;

pub async fn run(mut terminal: DefaultTerminal) -> anyhow::Result<()> {
    // Initialize channels
    let (action_tx, mut action_rx) = tokio::sync::mpsc::channel::<anyhow::Result<Action>>(1024);
    let (cmd_tx, cmd_rx) = tokio::sync::mpsc::channel::<Command>(1024);

    let mut app = App::default();
    let api = ForgeAPI::init(false);

    // Initialize Executor
    let executor = Executor::new(Arc::new(api));
    executor.init(action_tx.clone(), cmd_rx).await;

    // Initial STDIN
    let event_reader = EventReader::new(Duration::from_millis(100));
    event_reader.init(action_tx.clone()).await;

    // Send initial Initialize action - workspace info will be read by executor
    action_tx.send(Ok(Action::Initialize)).await?;
    loop {
        let render_app = app.clone();
        terminal.draw(|frame| {
            Widget::render(render_app.clone(), frame.area(), frame.buffer_mut());
        })?;

        if let Some(action) = action_rx.recv().await {
            let cmd = app.update(action?);
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
