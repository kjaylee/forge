use std::time::Duration;

use derive_more::From;

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
    Interval {
        // FIXME: Use chrono
        // FIXME: Drop Option
        duration: Option<Duration>,
    },
    CancelInterval {
        id: u64,
    },
}

impl Command {
    pub fn and_then(self, other: Command) -> Command {
        match self {
            Command::And(mut commands) => {
                commands.push(other);
                Command::And(commands)
            }
            _ => Command::And(vec![self, other]),
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_command_and_with_two_commands() {
        let fixture = Command::Empty.and_then(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_chaining() {
        let fixture = Command::Empty
            .and_then(Command::Exit)
            .and_then(Command::ReadWorkspace);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit, Command::ReadWorkspace]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_with_existing_and() {
        let fixture = Command::And(vec![Command::Empty]).and_then(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Exit]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_command_and_complex_chaining() {
        let fixture = Command::ChatMessage("hello".to_string())
            .and_then(Command::ReadWorkspace)
            .and_then(Command::Empty)
            .and_then(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![
            Command::ChatMessage("hello".to_string()),
            Command::ReadWorkspace,
            Command::Empty,
            Command::Exit,
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_chat_command_and() {
        let fixture = Command::Empty.and_then(Command::ChatMessage("test".to_string()));
        let actual = fixture;
        let expected = Command::And(vec![
            Command::Empty,
            Command::ChatMessage("test".to_string()),
        ]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_command_and() {
        let fixture = Command::Empty.and_then(Command::Empty);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Empty]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_help_command_and() {
        let fixture = Command::Empty.and_then(Command::Empty);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Empty]);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_settings_command_and() {
        let fixture = Command::Empty.and_then(Command::Empty);
        let actual = fixture;
        let expected = Command::And(vec![Command::Empty, Command::Empty]);
        assert_eq!(actual, expected);
    }
}
