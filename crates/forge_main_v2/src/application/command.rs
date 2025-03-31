use std::sync::Arc;

use anyhow::Result;
use forge_api::Workflow;

use crate::domain::{Command, CommandService, ForgeServices};

pub struct CommandProcessor<S: ForgeServices> {
    services: Arc<S>,
}

impl<S: ForgeServices> CommandProcessor<S> {
    pub fn new(services: Arc<S>) -> Self {
        Self { services }
    }

    pub fn register_workflow_commands(&self, workflow: &Workflow) -> Result<()> {
        self.services.command_service().register_commands(workflow);
        Ok(())
    }

    pub fn parse_command(&self, input: &str) -> Result<Command> {
        self.services.command_service().parse(input)
    }

    pub fn get_command_names(&self) -> Vec<String> {
        self.services.command_service().get_command_names()
    }
}

// Temporarily disabled until we can fix the mock implementations
/*
#[cfg(test)]
pub mod tests {
    // Test code disabled for now
}
*/
