use std::path::Path;

use anyhow::{Context, Result};
use forge_main_neo::{App, Runtime};
use tracing::debug;

fn main() -> Result<()> {
    let terminal = ratatui::init();
    let logger = forge_tracker::init_tracing(Path::new(".").to_path_buf())
        .context("failed to initialize logger")?;

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::EnableMouseCapture
    )?;

    let app_result = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .context("failed to build runtime")?
        .block_on(async {
            let app = App::new();
            let mut runtime = Runtime::new();
            runtime
                .run(terminal, app)
                .await
                .context("failed to run runtime")
        });

    debug!(app = ?app_result, "App finished");

    ratatui::crossterm::execute!(
        std::io::stdout(),
        ratatui::crossterm::event::DisableMouseCapture
    )?;

    drop(logger);
    ratatui::restore();

    app_result
}
