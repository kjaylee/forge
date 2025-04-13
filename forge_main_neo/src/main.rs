use anyhow::Context;
use forge_main_neo::App;

fn main() -> anyhow::Result<()> {
    let mut terminal = ratatui::init();
    let mut app = App::new();
    let app_result = app.run(&mut terminal).context("app loop failed");
    ratatui::restore();
    app_result
}
