pub mod application;
pub mod domain;
pub mod infrastructure;
pub mod presentation;

use std::sync::Arc;

use forge_api::{ForgeAPI, API};
use presentation::Cli;

use crate::domain::ForgeServices;
use crate::infrastructure::{ForgeCommandService, StandardForgeServices, TerminalUI};
use crate::presentation::ForgeTerminal;

// Service factory
pub struct ForgeServiceFactory;

impl ForgeServiceFactory {
    pub fn create_services(restricted: bool) -> impl domain::ForgeServices {
        let api = Arc::new(ForgeAPI::init(restricted));
        StandardForgeServices::new(api)
    }
}

// Create public API for ease of use
pub fn create_terminal(
    cli: Cli,
) -> anyhow::Result<ForgeTerminal<impl domain::ForgeServices, TerminalUI>> {
    // Initialize services
    let services = Arc::new(ForgeServiceFactory::create_services(cli.restricted));

    // Create command service for completions
    let command_service = Arc::new(ForgeCommandService::new()) as Arc<dyn domain::CommandService>;

    // Create UI with the command service for completions
    let ui = Arc::new(
        TerminalUI::new(&services.api().environment()).with_command_service(command_service),
    );

    // Create and return terminal instance
    Ok(ForgeTerminal::new(services, ui, cli))
}
