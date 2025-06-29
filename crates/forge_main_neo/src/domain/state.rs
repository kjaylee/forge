use derive_setters::Setters;
use edtui::{EditorState, Index2};

use crate::domain::{Message, Route, Workspace};

#[derive(Clone, Default, Setters)]
pub struct State {
    pub workspace: Workspace,
    pub current_route: Route,
    pub editor_state: EditorState,
    pub messages: Vec<Message>,
}

impl State {
    /// Navigate to the next route
    pub fn navigate_next(&mut self) {
        self.current_route = self.current_route.next();
    }

    /// Navigate to the previous route
    pub fn navigate_previous(&mut self) {
        self.current_route = self.current_route.previous();
    }

    /// Get editor lines as strings
    pub fn editor_lines(&self) -> Vec<String> {
        self.editor_state
            .lines
            .iter_row()
            .map(|row| row.iter().collect::<String>())
            .collect::<Vec<_>>()
    }

    /// Take lines from editor and clear it
    pub fn take_lines(&mut self) -> Vec<String> {
        let text = self.editor_lines();
        self.editor_state.lines.clear();
        self.editor_state.cursor = Index2::default();
        text
    }

    /// Add a user message to the chat
    pub fn add_user_message(&mut self, message: String) {
        self.messages.push(Message::User(message));
    }

    /// Add an assistant message to the chat
    pub fn add_assistant_message(&mut self, message: String) {
        self.messages.push(Message::Assistant(message));
    }
}
