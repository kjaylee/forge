use std::sync::Arc;

use anyhow::Result;
use clap::Parser;
use forge::{Cli, UI};
use forge_api::{ForgeAPI, SignalManager};

#[tokio::main]
async fn main() -> Result<()> {
    // Initialize signal manager
    let signal_manager = Arc::new(SignalManager::new());
    
    // Set up signal handlers
    let signal_manager_clone = signal_manager.clone();
    tokio::spawn(async move {
        let mut ctrl_c = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::interrupt()).unwrap();
        let mut term = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate()).unwrap();
        
        loop {
            tokio::select! {
                _ = ctrl_c.recv() => {
                    signal_manager_clone.cancel();
                }
                _ = term.recv() => {
                    signal_manager_clone.exit();
                    break;
                }
            }
        }
    });
    
    // Initialize and run the UI with signal manager
    let cli = Cli::parse();
    let api = Arc::new(ForgeAPI::init(cli.restricted));
    let mut ui = UI::init(cli, api, signal_manager)?;
    ui.run().await?;

    Ok(())
}
