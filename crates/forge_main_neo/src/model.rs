use derive_more::From;
use edtui::{EditorState, Index2};
use ratatui::crossterm::event::Event;

#[derive(Default)]
pub struct State {
    pub messages: Vec<String>,
    pub editor: EditorState,
    pub exit: bool,
    pub current_branch: Option<String>,
    pub current_dir: Option<String>,
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
}

#[derive(From, PartialEq, Eq)]
pub enum Command {
    Chat(String),
    ReadWorkspace,
    Empty,
    Exit,
}
