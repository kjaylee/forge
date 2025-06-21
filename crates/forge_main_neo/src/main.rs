use color_eyre::Result;
use forge_main_neo::App;
use ratatui::DefaultTerminal;
use ratatui::crossterm::event::{self, Event, KeyCode, KeyModifiers};

fn main() -> Result<()> {
    color_eyre::install()?;
    let terminal = ratatui::init();
    let result = run(terminal);
    ratatui::restore();
    result
}

fn run(mut terminal: DefaultTerminal) -> Result<()> {
    let mut app = App::default();

    loop {
        terminal.draw(|frame| {
            frame.render_widget(&mut app, frame.area());
        })?;

        match event::read()? {
            Event::Key(event) => {
                if event.code == KeyCode::Char('c')
                    && event.modifiers.contains(KeyModifiers::CONTROL)
                {
                    {
                        break Ok(());
                    }
                } else {
                    app.on_key_event(event);
                }
            }
            Event::Mouse(event) => {
                app.on_mouse_event(event);
            }
            _ => {}
        }
    }
}
