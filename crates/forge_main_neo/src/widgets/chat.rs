use edtui::{EditorTheme, EditorView};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::widgets::{Block, Padding, Paragraph, StatefulWidget, Widget};

use crate::domain::{EditorStateExt, State};
use crate::widgets::message_list::MessageList;
use crate::widgets::spotlight::SpotlightWidget;
use crate::widgets::status_bar::StatusBar;
use crate::widgets::welcome::WelcomeWidget;

/// Chat widget that handles the chat interface with editor and message list
#[derive(Clone, Default)]
pub struct ChatWidget;

impl StatefulWidget for ChatWidget {
    type State = State;
    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut State,
    ) where
        Self: Sized,
    {
        // Create chat layout with messages area at top and user input area at bottom
        let chat_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(5)],
        );
        let [messages_area, user_area] = chat_layout.areas(area);

        // Messages area block (now at top)
        let message_block = Block::new();

        // Render welcome widget if no messages, otherwise render message list
        if state.messages.is_empty() {
            WelcomeWidget.render(message_block.inner(messages_area), buf, state);
        } else {
            MessageList.render(message_block.inner(messages_area), buf, state);
        }

        if state.spotlight.is_visible {
            SpotlightWidget.render(messages_area, buf, state)
        }

        // User input area block with status bar (now at bottom)
        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(
                "FORGE",
                state.editor.mode.name(),
                state.workspace.clone(),
            ));

        EditorView::new(&mut state.editor)
            .theme(
                EditorTheme::default()
                    .base(Style::reset())
                    .cursor_style(Style::default().fg(Color::Black).bg(Color::White))
                    .hide_status_line(),
            )
            .wrap(true)
            .render(user_block.inner(user_area), buf);

        // Render autocomplete suggestion overlay if available
        if state.editor.mode == edtui::EditorMode::Insert && !state.spotlight.is_visible {
            let current_text = state.editor.get_text();
            if let Some(suggestion) = state
                .command_history
                .get_autocomplete_suggestion(&current_text)
            {
                // Calculate position for autocomplete overlay
                let editor_area = user_block.inner(user_area);
                let cursor_pos = state.editor.cursor;

                // Only show if suggestion is longer than current text
                if suggestion.len() > current_text.len() {
                    let remaining_text = &suggestion[current_text.len()..];

                    // Create a paragraph with the suggestion text
                    let suggestion_paragraph = Paragraph::new(remaining_text)
                        .style(Style::default().fg(Color::DarkGray))
                        .wrap(ratatui::widgets::Wrap { trim: false });

                    // Calculate the area for the suggestion starting from cursor position
                    let suggestion_rect = ratatui::layout::Rect {
                        x: editor_area.x + cursor_pos.col as u16,
                        y: editor_area.y + cursor_pos.row as u16,
                        width: editor_area.width.saturating_sub(cursor_pos.col as u16),
                        height: editor_area.height.saturating_sub(cursor_pos.row as u16),
                    };

                    // Ensure we don't render outside the editor area
                    let suggestion_area = editor_area.intersection(suggestion_rect);
                    if suggestion_area.width > 0 && suggestion_area.height > 0 {
                        suggestion_paragraph.render(suggestion_area, buf);
                    }
                }
            }
        }

        // Render blocks
        message_block.render(messages_area, buf);
        user_block.render(user_area, buf);
    }
}
