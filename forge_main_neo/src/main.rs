use anyhow::Context;
use forge_main_neo::App;

fn main() -> anyhow::Result<()> {
    let mut terminal = ratatui::init();

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::EnableMouseCapture
    )?;

    let mut app = App::default();
    let app_result = app.run(&mut terminal).context("app loop failed");

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::DisableMouseCapture
    )?;
    ratatui::restore();

    app_result
}
