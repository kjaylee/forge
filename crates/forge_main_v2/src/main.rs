use clap::Parser;
use forge_main_v2::presentation::Cli;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Parse CLI arguments
    let cli = Cli::parse();

    // Create and run terminal
    let mut terminal = forge_main_v2::create_terminal(cli)?;
    terminal.run().await
}
