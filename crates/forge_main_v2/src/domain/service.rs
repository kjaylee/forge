use anyhow::Result;
use async_trait::async_trait;
use forge_api::{Workflow, API};

use super::command::{Command, CommandDefinition};

/// Service interface for command parsing and management
#[async_trait]
pub trait CommandService: Send + Sync {
    fn parse(&self, input: &str) -> Result<Command>;
    fn register_commands(&self, workflow: &Workflow);
    fn get_command_names(&self) -> Vec<String>;
    fn list_commands(&self) -> Vec<CommandDefinition>;
}

/// Core service trait that provides access to application services
pub trait ForgeServices: Send + Sync + 'static {
    type API: API;
    type CommandService: CommandService;

    fn api(&self) -> &Self::API;
    fn command_service(&self) -> &Self::CommandService;
}
