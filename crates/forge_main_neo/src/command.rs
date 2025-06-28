use std::any::{Any, TypeId};

use derive_more::From;

/// Unified application commands
#[derive(Clone, From, PartialEq, Eq, Debug)]
pub enum Command {
    // Application-level commands
    ReadWorkspace,
    Empty,
    Exit,
    And(Vec<Command>),
    Tagged(Box<Command>, TypeId),

    // Chat commands
    SendMessage(String),
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
        let fixture = Command::SendMessage("hello".to_string())
            .and(Command::ReadWorkspace)
            .and(Command::Empty)
            .and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![
            Command::SendMessage("hello".to_string()),
            Command::ReadWorkspace,
            Command::Empty,
            Command::Exit,
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_chat_command_and() {
        let fixture = Command::Empty.and(Command::SendMessage("test".to_string()));
        let actual = fixture;
        let expected = Command::And(vec![
            Command::Empty,
            Command::SendMessage("test".to_string()),
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_command_and() {
        let fixture = Command::Empty.and(Command::Empty);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Empty]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_help_command_and() {
        let fixture = Command::Empty.and(Command::Empty);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Empty]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_settings_command_and() {
        let fixture = Command::Empty.and(Command::Empty);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Empty]);
        assert_eq!(actual, expected);
    }
}
