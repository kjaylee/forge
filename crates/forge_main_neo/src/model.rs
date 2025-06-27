use derive_more::From;
use edtui::{EditorState, Index2};
use ratatui::crossterm::event::Event;

use crate::widgets::Route;

#[derive(Default)]
pub struct State {
    pub messages: Vec<String>,
    pub editor: EditorState,
    pub current_branch: Option<String>,
    pub current_dir: Option<String>,
    pub current_route: Route,
}

impl State {
    pub fn editor_lines(&self) -> Vec<String> {
        self.editor
            .lines
            .iter_row()
            .map(|row| row.iter().collect::<String>())
            .collect::<Vec<_>>()
    }

    pub fn take_lines(&mut self) -> Vec<String> {
        let text = self.editor_lines();
        self.editor.lines.clear();
        self.editor.cursor = Index2::default();
        text
    }
}

#[derive(From)]
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
    NavigateToRoute(Route),
    NavigateNext,
    NavigatePrevious,
}

#[derive(From, PartialEq, Eq, Debug)]
pub enum Command {
    Chat(String),
    ReadWorkspace,
    Empty,
    Exit,
    And(Vec<Command>),
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
        let fixture = Command::Chat("hello".to_string())
            .and(Command::ReadWorkspace)
            .and(Command::Empty)
            .and(Command::Exit);
        let actual = fixture;
        let expected = Command::And(vec![
            Command::Chat("hello".to_string()),
            Command::ReadWorkspace,
            Command::Empty,
            Command::Exit,
        ]);
        assert_eq!(actual, expected);
    }
}
