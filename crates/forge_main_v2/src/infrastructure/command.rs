use std::sync::{Arc, Mutex};

use anyhow::Result;
use forge_api::Workflow;

use crate::domain::{Command, CommandDefinition, CommandPayload, CommandService};

pub struct ForgeCommandService {
    commands: Arc<Mutex<Vec<CommandDefinition>>>,
}

impl Default for ForgeCommandService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeCommandService {
    pub fn new() -> Self {
        Self { commands: Arc::new(Mutex::new(Self::default_commands())) }
    }

    fn default_commands() -> Vec<CommandDefinition> {
        vec![
            CommandDefinition {
                name: "/new".to_string(),
                description: "Start a new conversation".to_string(),
                value: None,
            },
            CommandDefinition {
                name: "/info".to_string(),
                description: "Display information about current session".to_string(),
                value: None,
            },
            CommandDefinition {
                name: "/exit".to_string(),
                description: "Exit the program".to_string(),
                value: None,
            },
            CommandDefinition {
                name: "/models".to_string(),
                description: "List available models".to_string(),
                value: None,
            },
            CommandDefinition {
                name: "/dump".to_string(),
                description: "Dump current conversation to file".to_string(),
                value: None,
            },
        ]
    }

    fn extract_command_value(&self, command: &CommandDefinition, parts: &[&str]) -> Option<String> {
        if parts.is_empty() {
            return None;
        }

        // If a predefined value exists, use that
        if let Some(ref value) = command.value {
            return Some(value.clone());
        }

        // Otherwise, join the remaining parts
        let value = parts.join(" ");
        if value.is_empty() {
            None
        } else {
            Some(value)
        }
    }

    fn find(&self, command_name: &str) -> Option<CommandDefinition> {
        self.commands
            .lock()
            .unwrap()
            .iter()
            .find(|c| c.name == command_name)
            .cloned()
    }
}

impl CommandService for ForgeCommandService {
    fn parse(&self, input: &str) -> Result<Command> {
        let trimmed = input.trim();
        if !trimmed.starts_with('/') {
            return Ok(Command::Message(trimmed.to_string()));
        }

        match trimmed {
            "/new" => Ok(Command::New),
            "/info" => Ok(Command::Info),
            "/exit" => Ok(Command::Exit),
            "/models" => Ok(Command::Models),
            "/dump" => Ok(Command::Dump),
            text => {
                let parts = text.split_ascii_whitespace().collect::<Vec<&str>>();

                if let Some(command_name) = parts.first() {
                    if let Some(command) = self.find(command_name) {
                        let value = self.extract_command_value(&command, &parts[1..]);

                        // Check if this is a mode command
                        if let Some(mode_name) = command.name.strip_prefix('/') {
                            if command.description.contains("[MODE]") {
                                return Ok(Command::Custom(CommandPayload {
                                    name: "mode".to_string(),
                                    value: Some(mode_name.to_string()),
                                }));
                            }
                        }

                        // Regular command
                        let name = command.name.strip_prefix('/').unwrap().to_string();
                        Ok(Command::Custom(CommandPayload { name, value }))
                    } else {
                        Err(anyhow::anyhow!("{} is not a valid command", command_name))
                    }
                } else {
                    Err(anyhow::anyhow!("Invalid command format"))
                }
            }
        }
    }

    fn register_commands(&self, workflow: &Workflow) {
        let mut guard = self.commands.lock().unwrap();
        let mut commands = Self::default_commands();

        // Add mode commands from workflow
        for mode in &workflow.modes {
            commands.push(CommandDefinition {
                name: mode.command.clone(),
                description: format!("[MODE] {}", mode.description),
                value: None,
            });
        }

        // Add custom commands from workflow
        commands.extend(
            workflow
                .commands
                .clone()
                .into_iter()
                .map(|cmd| CommandDefinition {
                    name: format!("/{}", cmd.name),
                    description: format!("[COMMAND] {}", cmd.description),
                    value: cmd.value.clone(),
                }),
        );

        // Sort and replace commands
        commands.sort_by(|a, b| a.name.cmp(&b.name));
        *guard = commands;
    }

    fn get_command_names(&self) -> Vec<String> {
        self.commands
            .lock()
            .unwrap()
            .iter()
            .map(|cmd| cmd.name.clone())
            .collect()
    }

    fn list_commands(&self) -> Vec<CommandDefinition> {
        self.commands.lock().unwrap().clone()
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_parse_message() {
        let fixture = ForgeCommandService::default();

        let actual = fixture.parse("Hello world").unwrap();
        match actual {
            Command::Message(text) => assert_eq!(text, "Hello world"),
            _ => panic!("Expected Message command"),
        }
    }

    #[test]
    fn test_parse_built_in_commands() {
        let fixture = ForgeCommandService::default();

        let test_cases = vec![
            ("/new", Command::New),
            ("/info", Command::Info),
            ("/exit", Command::Exit),
            ("/models", Command::Models),
            ("/dump", Command::Dump),
        ];

        for (input, expected) in test_cases {
            let actual = fixture.parse(input).unwrap();
            match (actual, expected) {
                (Command::New, Command::New) => {}
                (Command::Info, Command::Info) => {}
                (Command::Exit, Command::Exit) => {}
                (Command::Models, Command::Models) => {}
                (Command::Dump, Command::Dump) => {}
                _ => panic!("Command mismatch for {}", input),
            }
        }
    }

    #[test]
    fn test_register_mode_commands() {
        let fixture = ForgeCommandService::default();

        let workflow = Workflow {
            modes: vec![
                forge_api::ModeConfig {
                    name: "ACT".to_string(),
                    description: "Action mode".to_string(),
                    command: "/act".to_string(),
                },
                forge_api::ModeConfig {
                    name: "PLAN".to_string(),
                    description: "Planning mode".to_string(),
                    command: "/plan".to_string(),
                },
            ],
            ..Default::default()
        };

        fixture.register_commands(&workflow);

        let commands = fixture.get_command_names();
        assert!(commands.contains(&"/act".to_string()));
        assert!(commands.contains(&"/plan".to_string()));

        // Test parsing a mode command
        let actual = fixture.parse("/act").unwrap();
        match actual {
            Command::Custom(payload) => {
                assert_eq!(payload.name, "mode");
                assert_eq!(payload.value, Some("act".to_string()));
            }
            _ => panic!("Expected Custom command for mode"),
        }
    }
}
