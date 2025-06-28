use edtui::{EditorEventHandler, EditorMode, EditorState, EditorTheme, EditorView, Index2};
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, MouseEvent};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Padding, Widget};

use crate::command::Command;
use crate::widgets::autocomplete::{AutoComplete, AutocompletePopup};
use crate::widgets::message_list::{Message, MessageList};
use crate::widgets::status_bar::StatusBar;

/// Chat widget that handles the chat interface with editor and message list
#[derive(Clone, derive_setters::Setters)]
#[setters(strip_option, into)]
pub struct Chat {
    editor: EditorEventHandler,
    pub messages: Vec<Message>,
    pub editor_state: EditorState,
    pub autocomplete: AutoComplete,
}

impl Default for Chat {
    fn default() -> Self {
        let mut editor_state = EditorState::default();
        // Start the editor in Insert mode instead of Normal mode
        editor_state.mode = EditorMode::Insert;

        Self {
            editor: EditorEventHandler::default(),
            messages: Vec::new(),
            editor_state,
            autocomplete: AutoComplete::default(),
        }
    }
}

impl Chat {
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

    /// Check if current input starts with slash command
    fn is_slash_command_input(&self) -> bool {
        let lines = self.editor_lines();
        if let Some(first_line) = lines.first() {
            first_line.starts_with('/')
        } else {
            false
        }
    }

    /// Get current slash command filter text
    fn get_slash_command_filter(&self) -> String {
        let lines = self.editor_lines();
        if let Some(first_line) = lines.first() {
            if let Some(stripped) = first_line.strip_prefix('/') {
                stripped.to_string()
            } else {
                String::new()
            }
        } else {
            String::new()
        }
    }

    /// Handle key events for the chat interface
    pub fn handle_key_event(&mut self, event: KeyEvent) -> Command {
        // Handle autocomplete navigation when popup is active
        if self.autocomplete.is_active {
            match event.code {
                KeyCode::Up => {
                    self.autocomplete.select_previous();
                    return Command::Empty;
                }
                KeyCode::Down => {
                    self.autocomplete.select_next();
                    return Command::Empty;
                }
                KeyCode::Enter => {
                    if let Some(selected_command) = self.autocomplete.get_selected_command() {
                        let command_text = format!("/{}", selected_command.name);
                        // Clear editor and insert command
                        self.editor_state.lines.clear();
                        self.editor_state.cursor = Index2::default();
                        for ch in command_text.chars() {
                            self.editor.on_key_event(
                                KeyEvent::new(KeyCode::Char(ch), event.modifiers),
                                &mut self.editor_state,
                            );
                        }
                        self.autocomplete.deactivate();
                        return Command::Empty;
                    }
                }
                KeyCode::Esc => {
                    self.autocomplete.deactivate();
                    return Command::Empty;
                }
                _ => {
                    // Continue with normal editor handling for other keys
                }
            }
        }

        // Submit message on Enter in Normal mode
        if event.code == KeyCode::Enter && self.editor_state.mode == EditorMode::Normal {
            let message = self.take_lines().join("\n");
            self.messages.push(Message::User(message.clone()));
            self.autocomplete.deactivate(); // Ensure popup is closed
            if message.trim().is_empty() {
                Command::Empty
            } else {
                Command::SendMessage(message)
            }
        } else {
            // Handle editor events
            self.editor.on_key_event(event, &mut self.editor_state);

            // Check if we should activate/update autocomplete popup
            if self.is_slash_command_input() {
                let filter_text = self.get_slash_command_filter();
                if !self.autocomplete.is_active {
                    self.autocomplete.activate(filter_text);
                } else {
                    self.autocomplete.update_filter(filter_text);
                }
            } else if self.autocomplete.is_active {
                self.autocomplete.deactivate();
            }

            Command::Empty
        }
    }

    /// Handle mouse events for the chat interface
    pub fn handle_mouse_event(&mut self, event: MouseEvent) -> Command {
        self.editor.on_mouse_event(event, &mut self.editor_state);
        Command::Empty
    }

    /// Handle crossterm events for the chat interface
    pub fn handle_event(&mut self, event: Event) -> Command {
        match event {
            Event::Key(key_event) => self.handle_key_event(key_event),
            Event::Mouse(mouse_event) => self.handle_mouse_event(mouse_event),
            _ => Command::Empty,
        }
    }
}

impl Chat {
    /// Add a user message to the chat
    pub fn add_user_message(&mut self, message: String) {
        self.messages.push(Message::User(message));
    }

    /// Add an assistant message to the chat
    pub fn add_assistant_message(&mut self, message: String) {
        self.messages.push(Message::Assistant(message));
    }
}

impl Widget for Chat {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        // Create chat layout with messages area at top and user input area at bottom
        let chat_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(5)],
        );
        let [messages_area, user_area] = chat_layout.areas(area);

        // Messages area block (now at top)
        let content_block = Block::bordered()
            .borders(Borders::TOP | Borders::LEFT | Borders::RIGHT)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        // Render message list
        MessageList::new(self.messages.clone()).render(content_block.inner(messages_area), buf);

        // User input area block with status bar (now at bottom)
        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            // .borders(Borders::TOP | Borders::LEFT | Borders::RIGHT | Borders::BOTTOM)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(
                "FORGE",
                self.editor_state.mode.name(),
                None, // No branch info in Widget impl
                None, // No dir info in Widget impl
            ));

        // Note: EditorView needs mutable access to state, which we can't provide in
        // Widget trait This will need to be addressed differently - perhaps by
        // storing editor state separately For now, we'll create a temporary
        // mutable copy for rendering
        let mut temp_editor = self.editor_state.clone();
        EditorView::new(&mut temp_editor)
            .theme(
                EditorTheme::default()
                    .base(Style::reset())
                    .cursor_style(Style::default().fg(Color::Black).bg(Color::White))
                    .hide_status_line(),
            )
            .wrap(true)
            .render(user_block.inner(user_area), buf);

        // Render blocks
        content_block.render(messages_area, buf);
        user_block.render(user_area, buf);

        // Render autocomplete popup if active
        AutocompletePopup::new(&self.autocomplete, area, user_area).render(area, buf);
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_chat_setters() {
        let fixture = Chat::default();

        // Test setters work with the derive_setters attributes
        let messages = vec![
            Message::User("Hello".to_string()),
            Message::Assistant("World".to_string()),
        ];
        let editor = EditorState::default();

        let fixture = fixture
            .messages(messages.clone())
            .editor_state(editor.clone());

        assert_eq!(fixture.messages, messages);
        // EditorState doesn't implement PartialEq, so we just verify it was set
        assert_eq!(fixture.editor_state.lines.len(), editor.lines.len());
    }

    #[test]
    fn test_chat_default_starts_in_insert_mode() {
        let fixture = Chat::default();

        // Verify that the editor starts in Insert mode instead of Normal mode
        assert_eq!(fixture.editor_state.mode, EditorMode::Insert);
    }
}
