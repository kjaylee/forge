use std::collections::VecDeque;
use std::time::Duration;

use chrono::{DateTime, Utc};
use edtui::EditorState;
use forge_api::{ChatResponse, ConversationId};
use throbber_widgets_tui::ThrobberState;
use tui_scrollview::ScrollViewState;

use crate::domain::spotlight::SpotlightState;
use crate::domain::{CancelId, EditorStateExt, Message, Workspace};

/// Command history with LRU storage and navigation tracking
#[derive(Clone, Debug)]
pub struct CommandHistory {
    commands: VecDeque<String>,
    current_index: Option<usize>,
    max_size: usize,
}

impl Default for CommandHistory {
    fn default() -> Self {
        Self {
            commands: VecDeque::new(),
            current_index: None,
            max_size: 100,
        }
    }
}

impl CommandHistory {
    /// Add a command to history (LRU - most recent at front)
    pub fn add_command(&mut self, command: String) {
        if command.trim().is_empty() {
            return;
        }

        // Remove existing instance if present
        if let Some(pos) = self.commands.iter().position(|c| c == &command) {
            self.commands.remove(pos);
        }

        // Add to front
        self.commands.push_front(command);

        // Enforce size limit
        if self.commands.len() > self.max_size {
            self.commands.pop_back();
        }

        // Reset navigation
        self.current_index = None;
    }

    /// Navigate to previous command (up arrow)
    pub fn navigate_up(&mut self) -> Option<String> {
        if self.commands.is_empty() {
            return None;
        }

        match self.current_index {
            None => {
                // Start navigation from most recent
                self.current_index = Some(0);
                self.commands.front().cloned()
            }
            Some(index) => {
                // Move to older command if possible
                if index + 1 < self.commands.len() {
                    self.current_index = Some(index + 1);
                    self.commands.get(index + 1).cloned()
                } else {
                    // Stay at oldest command
                    self.commands.get(index).cloned()
                }
            }
        }
    }

    /// Navigate to next command (down arrow)
    pub fn navigate_down(&mut self) -> Option<String> {
        match self.current_index {
            None => None,
            Some(0) => {
                // Reset to no selection (empty input)
                self.current_index = None;
                Some(String::new())
            }
            Some(index) => {
                // Move to newer command
                self.current_index = Some(index - 1);
                self.commands.get(index - 1).cloned()
            }
        }
    }

    /// Get autocomplete suggestion for current input
    pub fn get_autocomplete_suggestion(&self, current_input: &str) -> Option<String> {
        if current_input.trim().is_empty() {
            return None;
        }

        // Find first command that starts with current input
        self.commands
            .iter()
            .find(|cmd| cmd.starts_with(current_input) && cmd != &current_input)
            .cloned()
    }

    /// Reset navigation state (called when user types)
    pub fn reset_navigation(&mut self) {
        self.current_index = None;
    }
}

#[derive(Clone)]
pub struct State {
    pub workspace: Workspace,
    pub editor: EditorState,
    pub messages: Vec<Message>,
    pub spinner: ThrobberState,
    pub timer: Option<Timer>,
    pub show_spinner: bool,
    pub spotlight: SpotlightState,
    pub conversation: ConversationState,
    pub chat_stream: Option<CancelId>,
    pub message_scroll_state: ScrollViewState,
    pub command_history: CommandHistory,
}

impl Default for State {
    fn default() -> Self {
        let prompt_editor = EditorState::default();

        Self {
            workspace: Default::default(),
            editor: prompt_editor,
            messages: Default::default(),
            spinner: Default::default(),
            timer: Default::default(),
            show_spinner: Default::default(),
            spotlight: Default::default(),
            conversation: Default::default(),
            chat_stream: None,
            message_scroll_state: ScrollViewState::default(),
            command_history: CommandHistory::default(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Timer {
    pub start_time: DateTime<Utc>,
    pub current_time: DateTime<Utc>,
    pub duration: Duration,
    pub cancel: CancelId,
}

impl State {
    /// Get editor lines as strings
    pub fn editor_lines(&self) -> Vec<String> {
        self.editor.get_lines()
    }

    /// Take lines from editor and clear it
    pub fn take_lines(&mut self) -> Vec<String> {
        let text = self.editor_lines();
        self.editor.clear();
        text
    }

    /// Add a user message to the chat
    pub fn add_user_message(&mut self, message: String) {
        self.messages.push(Message::User(message));
        // Auto-scroll to bottom when new message is added
        self.message_scroll_state.scroll_to_bottom();
    }

    /// Add an assistant message to the chat
    pub fn add_assistant_message(&mut self, message: ChatResponse) {
        self.messages.push(Message::Assistant(message));
        // Auto-scroll to bottom when new message is added
        self.message_scroll_state.scroll_to_bottom();
    }
}

#[derive(Clone, Debug, Default)]
pub struct ConversationState {
    pub conversation_id: Option<ConversationId>,
    pub is_first: bool,
}

impl ConversationState {
    pub fn init_conversation(&mut self, conversation_id: ConversationId) {
        self.conversation_id = Some(conversation_id);
        self.is_first = false;
    }
}
