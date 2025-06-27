use edtui::{EditorEventHandler, EditorMode, EditorTheme, EditorView};
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, MouseEvent};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Padding, Widget};

use crate::model::{Command, State};
use crate::widgets::message_list::MessageList;
use crate::widgets::status_bar::StatusBar;

/// Chat widget that handles the chat interface with editor and message list
#[derive(Default)]
pub struct Chat {
    editor: EditorEventHandler,
    state: State,
}


impl Chat {
    /// Handle key events for the chat interface
    pub fn handle_key_event(&mut self, event: KeyEvent) -> Command {
        // Submit message on Enter in Normal mode
        if event.code == KeyCode::Enter && self.state.editor.mode == EditorMode::Normal {
            let message = self.state.take_lines().join("\n");
            self.state.messages.push(message.clone());
            if message.trim().is_empty() {
                Command::Empty
            } else {
                Command::Chat(message)
            }
        } else {
            // Handle editor events
            self.editor.on_key_event(event, &mut self.state.editor);
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

impl Widget for &Chat {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        // Create chat layout with messages area and user input area
        let chat_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(5)],
        );
        let [messages_area, user_area] = chat_layout.areas(area);

        // Messages area block
        let content_block = Block::bordered()
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT | Borders::TOP)
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

        // User input area block with status bar
        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(
                "FORGE",
                self.state.editor.mode.name(),
                self.state.current_branch.clone(),
                self.state.current_dir.clone(),
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
    }
}
