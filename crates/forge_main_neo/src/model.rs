use std::any::{Any, TypeId};

use derive_more::From;
use ratatui::crossterm::event::Event;

use crate::widgets::{chat, help, router, settings};

/// Top-level application actions that wrap route-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum Action {
    CrossTerm(Event),
    Initialize,
    Workspace {
        current_dir: Option<String>,
        current_branch: Option<String>,
    },
    ChatResponse {
        message: String,
    },
    // Route-specific action containers
    Router(router::Action),
    Chat(chat::Action),
    Help(help::Action),
    Settings(settings::Action),
}

/// Top-level application commands that wrap route-specific commands
#[derive(Clone, From, PartialEq, Eq, Debug)]
pub enum Command {
    ReadWorkspace,
    Empty,
    Exit,
    And(Vec<Command>),
    Tagged(Box<Command>, TypeId),
    // Route-specific command containers
    Router(router::Command),
    Chat(chat::Command),
    Help(help::Command),
    Settings(settings::Command),
}

impl Command {
    pub fn and(self, other: Command) -> Command {
        match self {
            Command::And(mut commands) => {
                commands.push(other);
                Command::And(commands)
            }
            _ => Command::And(vec![self, other]),
        }
    }

    pub fn tagged<T: Any>(self, t: T) -> Self {
        Command::Tagged(Box::new(self), t.type_id())
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
        let expected = Command::And(vec![Command::Empty, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_chaining() {
        let fixture = Command::Empty
            .and(Command::Exit)
            .and(Command::ReadWorkspace);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit, Command::ReadWorkspace]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_with_existing_and() {
        let fixture = Command::And(vec![Command::Empty]).and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_complex_chaining() {
        let fixture = Command::Chat(chat::Command::SendMessage("hello".to_string()))
            .and(Command::ReadWorkspace)
            .and(Command::Empty)
            .and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![
            Command::Chat(chat::Command::SendMessage("hello".to_string())),
            Command::ReadWorkspace,
            Command::Empty,
            Command::Exit,
        ]);
        assert_eq!(actual, expected);
    }
}
