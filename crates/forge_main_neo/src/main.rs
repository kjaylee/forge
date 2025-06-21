use color_eyre::Result;
use crossterm::event::{self, Event};
use forge_main_neo::App;
use ratatui::DefaultTerminal;

fn main() -> Result<()> {
    color_eyre::install()?;
    let terminal = ratatui::init();
    let result = run(terminal);
    ratatui::restore();
    result
}

fn run(mut terminal: DefaultTerminal) -> Result<()> {
    let app = App::default();
    loop {
        terminal.draw(|frame| {
            frame.render_widget(&app, frame.area());
        })?;
        if matches!(event::read()?, Event::Key(_)) {
            break Ok(());
        }
    }
}
