use edtui::{EditorEventHandler, EditorMode, EditorTheme, EditorView};
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, MouseEvent};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Padding, StatefulWidget, Widget};

use crate::model::{Command, State};
use crate::widgets::message_list::MessageList;
use crate::widgets::status_bar::StatusBar;

/// Chat widget that handles the chat interface with editor and message list
#[derive(Default)]
pub struct Chat {
    editor: EditorEventHandler,
}

impl Chat {
    /// Handle key events for the chat interface
    pub fn handle_key_event(&mut self, event: KeyEvent, state: &mut State) -> Command {
        // Submit message on Enter in Normal mode
        if event.code == KeyCode::Enter && state.editor.mode == EditorMode::Normal {
            let message = state.take_lines().join("\n");
            state.messages.push(message.clone());
            return Command::Chat(message);
        }

        // Handle editor events
        self.editor.on_key_event(event, &mut state.editor);
        Command::Empty
    }

    /// Handle mouse events for the chat interface
    pub fn handle_mouse_event(&mut self, event: MouseEvent, state: &mut State) -> Command {
        self.editor.on_mouse_event(event, &mut state.editor);
        Command::Empty
    }

    /// Handle crossterm events for the chat interface
    pub fn handle_event(&mut self, event: Event, state: &mut State) -> Command {
        match event {
            Event::Key(key_event) => self.handle_key_event(key_event, state),
            Event::Mouse(mouse_event) => self.handle_mouse_event(mouse_event, state),
            _ => Command::Empty,
        }
    }
}

impl StatefulWidget for &Chat {
    type State = State;

    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut Self::State,
    ) where
        Self: Sized,
    {
        // Create chat layout with messages area and user input area
        let chat_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(3)],
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
        MessageList::new(state.messages.clone()).render(content_block.inner(messages_area), buf);

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
                state.editor.mode.name(),
                state.current_branch.clone(),
                state.current_dir.clone(),
            ));

        // Render editor
        EditorView::new(&mut state.editor)
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
