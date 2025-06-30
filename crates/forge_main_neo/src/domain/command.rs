use std::time::Duration;

use derive_more::From;
use forge_api::{AgentId, ModelId};

use crate::domain::TimerId;

/// Unified application commands
#[derive(Default, Clone, From, PartialEq, Eq, Debug)]
pub enum Command {
    // Application-level commands
    ReadWorkspace,
    #[default]
    Empty,
    Exit,
    And(Vec<Command>),
    ChatMessage(String),
    Spotlight(SpotlightCommand),
    Interval {
        duration: Duration,
    },
    ClearInterval {
        id: TimerId,
    },
}

#[derive(Clone, From, PartialEq, Eq, Debug)]
pub enum SpotlightCommand {
    Model(ModelId),
    Agent(AgentId),
}

impl Command {
    pub fn and(self, other: Command) -> Command {
        Command::And(vec![self, other]).flatten()
    }

    /// Flattens nested commands into a single And command, with ultra
    /// optimization for single commands
    pub fn flatten(self) -> Command {
        let mut flattened = Vec::new();
        self.flatten_recursive(&mut flattened);

        // Ultra optimization: avoid allocation for single command
        match flattened.len() {
            0 => Command::Empty,
            1 => flattened.into_iter().next().unwrap(),
            _ => Command::And(flattened),
        }
    }

    fn flatten_recursive(self, collector: &mut Vec<Command>) {
        match self {
            Command::And(commands) => {
                // Recursively flatten nested And commands
                for command in commands {
                    command.flatten_recursive(collector);
                }
            }
            Command::Empty => {
                // Skip empty commands for optimization
            }
            command => {
                collector.push(command);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_command_and_with_two_commands() {
        let fixture = Command::Empty.and(Command::Exit);
        let actual = fixture;
        let expected = Command::Exit;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_chaining() {
        let fixture = Command::Empty
            .and(Command::Exit)
            .and(Command::ReadWorkspace);
        let actual = fixture;
        let expected = Command::And(vec![Command::Exit, Command::ReadWorkspace]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_with_existing_and() {
        let fixture = Command::And(vec![Command::Empty]).and(Command::Exit);
        let actual = fixture;
        let expected = Command::Exit;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_complex_chaining() {
        let fixture = Command::ChatMessage("hello".to_string())
            .and(Command::ReadWorkspace)
            .and(Command::Empty)
            .and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![
            Command::ChatMessage("hello".to_string()),
            Command::ReadWorkspace,
            Command::Exit,
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_chat_command_and() {
        let fixture = Command::Empty.and(Command::ChatMessage("test".to_string()));
        let actual = fixture;
        let expected = Command::ChatMessage("test".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_command_and() {
        let fixture = Command::Empty.and(Command::Empty);
        let actual = fixture;
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_help_command_and() {
        let fixture = Command::Empty.and(Command::Empty);
        let actual = fixture;
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_settings_command_and() {
        let fixture = Command::Empty.and(Command::Empty);
        let actual = fixture;
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_empty_command() {
        let fixture = Command::Empty;
        let actual = fixture.flatten();
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_single_command() {
        let fixture = Command::Exit;
        let actual = fixture.flatten();
        let expected = Command::Exit;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_single_and_command() {
        let fixture = Command::And(vec![Command::Exit]);
        let actual = fixture.flatten();
        let expected = Command::Exit;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_multiple_commands() {
        let fixture = Command::And(vec![
            Command::ReadWorkspace,
            Command::Exit,
            Command::ChatMessage("test".to_string()),
        ]);
        let actual = fixture.flatten();
        let expected = Command::And(vec![
            Command::ReadWorkspace,
            Command::Exit,
            Command::ChatMessage("test".to_string()),
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_nested_and_commands() {
        let fixture = Command::And(vec![
            Command::ReadWorkspace,
            Command::And(vec![
                Command::Exit,
                Command::ChatMessage("test".to_string()),
            ]),
            Command::And(vec![Command::ReadWorkspace]),
        ]);
        let actual = fixture.flatten();
        let expected = Command::And(vec![
            Command::ReadWorkspace,
            Command::Exit,
            Command::ChatMessage("test".to_string()),
            Command::ReadWorkspace,
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_with_empty_commands() {
        let fixture = Command::And(vec![
            Command::Empty,
            Command::ReadWorkspace,
            Command::Empty,
            Command::Exit,
            Command::Empty,
        ]);
        let actual = fixture.flatten();
        let expected = Command::And(vec![Command::ReadWorkspace, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_only_empty_commands() {
        let fixture = Command::And(vec![Command::Empty, Command::Empty, Command::Empty]);
        let actual = fixture.flatten();
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_deeply_nested_commands() {
        let fixture = Command::And(vec![
            Command::ReadWorkspace,
            Command::And(vec![
                Command::Exit,
                Command::And(vec![
                    Command::ChatMessage("nested".to_string()),
                    Command::And(vec![Command::ReadWorkspace]),
                ]),
            ]),
        ]);
        let actual = fixture.flatten();
        let expected = Command::And(vec![
            Command::ReadWorkspace,
            Command::Exit,
            Command::ChatMessage("nested".to_string()),
            Command::ReadWorkspace,
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_flatten_complex_mixed_scenario() {
        let fixture = Command::And(vec![
            Command::Empty,
            Command::And(vec![
                Command::ChatMessage("hello".to_string()),
                Command::Empty,
                Command::And(vec![Command::ReadWorkspace, Command::Empty]),
            ]),
            Command::Exit,
            Command::And(vec![Command::Empty]),
            Command::ChatMessage("world".to_string()),
        ]);
        let actual = fixture.flatten();
        let expected = Command::And(vec![
            Command::ChatMessage("hello".to_string()),
            Command::ReadWorkspace,
            Command::Exit,
            Command::ChatMessage("world".to_string()),
        ]);
        assert_eq!(actual, expected);
    }
}
