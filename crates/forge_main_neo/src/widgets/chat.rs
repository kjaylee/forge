use std::any::{Any, TypeId};

use derive_more::From;
use edtui::{EditorEventHandler, EditorMode, EditorTheme, EditorView};
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, MouseEvent};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Clear, Padding, Widget};

use crate::widgets::message_list::MessageList;
use crate::widgets::status_bar::StatusBar;

/// Represents a slash command
#[derive(Clone, Debug, PartialEq)]
pub struct SlashCommand {
    pub name: String,
    pub description: String,
}

impl SlashCommand {
    pub fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self { name: name.into(), description: description.into() }
    }
}

/// State for slash command popup
#[derive(Clone, Debug)]
pub struct SlashCommandState {
    pub is_active: bool,
    pub selected_index: usize,
    pub filter_text: String,
    pub available_commands: Vec<SlashCommand>,
    pub filtered_commands: Vec<SlashCommand>,
}

impl Default for SlashCommandState {
    fn default() -> Self {
        let available_commands = vec![
            SlashCommand::new("foo", "Execute foo command"),
            SlashCommand::new("bar", "Execute bar command"),
            SlashCommand::new("baz", "Execute baz command"),
        ];

        Self {
            is_active: false,
            selected_index: 0,
            filter_text: String::new(),
            filtered_commands: available_commands.clone(),
            available_commands,
        }
    }
}

impl SlashCommandState {
    pub fn activate(&mut self, filter_text: String) {
        self.is_active = true;
        self.filter_text = filter_text;
        self.selected_index = 0;
        self.update_filtered_commands();
    }

    pub fn deactivate(&mut self) {
        self.is_active = false;
        self.filter_text.clear();
        self.selected_index = 0;
        self.filtered_commands = self.available_commands.clone();
    }

    pub fn update_filter(&mut self, filter_text: String) {
        self.filter_text = filter_text;
        self.selected_index = 0;
        self.update_filtered_commands();
    }

    fn update_filtered_commands(&mut self) {
        self.filtered_commands = self
            .available_commands
            .iter()
            .filter(|cmd| cmd.name.contains(&self.filter_text))
            .cloned()
            .collect();
    }

    pub fn select_next(&mut self) {
        if !self.filtered_commands.is_empty() {
            self.selected_index = (self.selected_index + 1) % self.filtered_commands.len();
        }
    }

    pub fn select_previous(&mut self) {
        if !self.filtered_commands.is_empty() {
            self.selected_index = if self.selected_index == 0 {
                self.filtered_commands.len() - 1
            } else {
                self.selected_index - 1
            };
        }
    }

    pub fn get_selected_command(&self) -> Option<&SlashCommand> {
        self.filtered_commands.get(self.selected_index)
    }
}

/// Chat-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum Action {
    MessageAdded(String),
    EditorUpdated,
}

/// Chat-specific commands
#[derive(Clone, From, PartialEq, Eq, Debug)]
pub enum Command {
    SendMessage(String),
    Empty,
    And(Vec<Command>),
    Tagged(Box<Command>, TypeId),
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
use edtui::{EditorState, Index2};

#[derive(Default, derive_setters::Setters)]
#[setters(strip_option, into)]
pub struct State {
    pub messages: Vec<String>,
    pub editor: EditorState,
    pub slash_commands: SlashCommandState,
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

/// Chat widget that handles the chat interface with editor and message list
#[derive(Default)]
pub struct Chat {
    editor: EditorEventHandler,
    state: State,
}

impl Chat {
    /// Check if current input starts with slash command
    fn is_slash_command_input(&self) -> bool {
        let lines = self.state.editor_lines();
        if let Some(first_line) = lines.first() {
            first_line.starts_with('/')
        } else {
            false
        }
    }

    /// Get current slash command filter text
    fn get_slash_command_filter(&self) -> String {
        let lines = self.state.editor_lines();
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
        // Handle slash command navigation when popup is active
        if self.state.slash_commands.is_active {
            match event.code {
                KeyCode::Up => {
                    self.state.slash_commands.select_previous();
                    return Command::Empty;
                }
                KeyCode::Down => {
                    self.state.slash_commands.select_next();
                    return Command::Empty;
                }
                KeyCode::Enter => {
                    if let Some(selected_command) = self.state.slash_commands.get_selected_command()
                    {
                        let command_text = format!("/{}", selected_command.name);
                        // Clear editor and insert command
                        self.state.editor.lines.clear();
                        self.state.editor.cursor = Index2::default();
                        for ch in command_text.chars() {
                            self.editor.on_key_event(
                                KeyEvent::new(KeyCode::Char(ch), event.modifiers),
                                &mut self.state.editor,
                            );
                        }
                        self.state.slash_commands.deactivate();
                        return Command::Empty;
                    }
                }
                KeyCode::Esc => {
                    self.state.slash_commands.deactivate();
                    return Command::Empty;
                }
                _ => {
                    // Continue with normal editor handling for other keys
                }
            }
        }

        // Submit message on Enter in Normal mode
        if event.code == KeyCode::Enter && self.state.editor.mode == EditorMode::Normal {
            let message = self.state.take_lines().join("\n");
            self.state.messages.push(message.clone());
            self.state.slash_commands.deactivate(); // Ensure popup is closed
            if message.trim().is_empty() {
                Command::Empty
            } else {
                Command::SendMessage(message)
            }
        } else {
            // Handle editor events
            self.editor.on_key_event(event, &mut self.state.editor);

            // Check if we should activate/update slash command popup
            if self.is_slash_command_input() {
                let filter_text = self.get_slash_command_filter();
                if !self.state.slash_commands.is_active {
                    self.state.slash_commands.activate(filter_text);
                } else {
                    self.state.slash_commands.update_filter(filter_text);
                }
            } else if self.state.slash_commands.is_active {
                self.state.slash_commands.deactivate();
            }

            Command::Empty
        }
    }

    /// Handle mouse events for the chat interface
    pub fn handle_mouse_event(&mut self, event: MouseEvent) -> Command {
        self.editor.on_mouse_event(event, &mut self.state.editor);
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
    /// Add a message to the chat
    pub fn add_message(&mut self, message: String) {
        self.state.messages.push(message);
    }

    /// Render slash command popup
    fn render_slash_command_popup(
        &self,
        area: ratatui::prelude::Rect,
        user_area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
    ) {
        if !self.state.slash_commands.is_active
            || self.state.slash_commands.filtered_commands.is_empty()
        {
            return;
        }

        // Calculate popup position (above the user input area)
        let popup_height = (self.state.slash_commands.filtered_commands.len() as u16).min(5) + 2; // +2 for borders
        let popup_area = ratatui::prelude::Rect {
            x: area.x + 1,
            y: user_area.y.saturating_sub(popup_height), // Position above the user input area
            width: area.width.saturating_sub(2).min(40),
            height: popup_height,
        };

        // Create popup block
        let popup_block = Block::bordered()
            .title("Commands")
            .border_style(Style::default().fg(Color::Cyan))
            .style(Style::default().bg(Color::Black));

        // Get inner area before rendering the block
        let inner_area = popup_block.inner(popup_area);

        // Render popup background
        Clear.render(popup_area, buf);
        popup_block.render(popup_area, buf);
        for (i, command) in self
            .state
            .slash_commands
            .filtered_commands
            .iter()
            .enumerate()
        {
            if i >= inner_area.height as usize {
                break;
            }

            let y = inner_area.y + i as u16;
            let style = if i == self.state.slash_commands.selected_index {
                Style::default().bg(Color::Blue).fg(Color::White)
            } else {
                Style::default()
            };

            let command_text = format!("/{} - {}", command.name, command.description);
            let truncated_text = if command_text.len() > inner_area.width as usize {
                format!(
                    "{}...",
                    &command_text[..inner_area.width.saturating_sub(3) as usize]
                )
            } else {
                command_text
            };

            for (j, ch) in truncated_text.chars().enumerate() {
                if j >= inner_area.width as usize {
                    break;
                }
                let cell = buf.cell_mut((inner_area.x + j as u16, y)).unwrap();
                cell.set_char(ch);
                cell.set_style(style);
            }
        }
    }

    /// Render the chat widget with shared application state
    pub fn render_with_state(
        &self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        current_branch: Option<String>,
        current_dir: Option<String>,
    ) {
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
        MessageList::new(self.state.messages.clone())
            .render(content_block.inner(messages_area), buf);

        // User input area block with status bar (now at bottom)
        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            .borders(Borders::TOP | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(
                "FORGE",
                self.state.editor.mode.name(),
                current_branch,
                current_dir,
            ));

        // Note: EditorView needs mutable access to state, which we can't provide in
        // Widget trait This will need to be addressed differently - perhaps by
        // storing editor state separately For now, we'll create a temporary
        // mutable copy for rendering
        let mut temp_editor = self.state.editor.clone();
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

        // Render slash command popup if active
        self.render_slash_command_popup(area, user_area, buf);
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_state_setters() {
        let fixture = State::default();

        // Test setters work with the derive_setters attributes
        let messages = vec!["Hello".to_string(), "World".to_string()];
        let editor = EditorState::default();

        let fixture = fixture.messages(messages.clone()).editor(editor.clone());

        assert_eq!(fixture.messages, messages);
        // EditorState doesn't implement PartialEq, so we just verify it was set
        assert_eq!(fixture.editor.lines.len(), editor.lines.len());
    }

    #[test]
    fn test_slash_command_creation() {
        let fixture = SlashCommand::new("test", "Test command");
        let actual = fixture;
        let expected = SlashCommand {
            name: "test".to_string(),
            description: "Test command".to_string(),
        };
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_slash_command_state_new() {
        let fixture = SlashCommandState::default();
        let actual = fixture.available_commands.len();
        let expected = 3;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_slash_command_state_filtering() {
        let mut fixture = SlashCommandState::default();
        fixture.update_filter("fo".to_string());
        let actual = fixture.filtered_commands.len();
        let expected = 1; // Only "foo" should match
        assert_eq!(actual, expected);
        assert_eq!(fixture.filtered_commands[0].name, "foo");
    }

    #[test]
    fn test_slash_command_state_navigation() {
        let mut fixture = SlashCommandState::default();
        fixture.activate("".to_string());

        // Test next selection
        fixture.select_next();
        let actual = fixture.selected_index;
        let expected = 1;
        assert_eq!(actual, expected);

        // Test previous selection
        fixture.select_previous();
        let actual = fixture.selected_index;
        let expected = 0;
        assert_eq!(actual, expected);

        // Test wrap around
        fixture.select_previous();
        let actual = fixture.selected_index;
        let expected = 2; // Should wrap to last item
        assert_eq!(actual, expected);
    }
}

impl Widget for &Chat {
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
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        // Render message list
        MessageList::new(self.state.messages.clone())
            .render(content_block.inner(messages_area), buf);

        // User input area block with status bar (now at bottom)
        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            .borders(Borders::TOP | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(
                "FORGE",
                self.state.editor.mode.name(),
                None, // No branch info in Widget impl
                None, // No dir info in Widget impl
            ));

        // Note: EditorView needs mutable access to state, which we can't provide in
        // Widget trait This will need to be addressed differently - perhaps by
        // storing editor state separately For now, we'll create a temporary
        // mutable copy for rendering
        let mut temp_editor = self.state.editor.clone();
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

        // Render slash command popup if active
        self.render_slash_command_popup(area, user_area, buf);
    }
}
