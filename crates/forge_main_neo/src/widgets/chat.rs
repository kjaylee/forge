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

                    // Split the remaining text into lines to handle wrapping properly
                    let available_width =
                        editor_area.width.saturating_sub(cursor_pos.col as u16) as usize;
                    let mut lines = text_to_lines(&remaining_text, available_width);

                    // Render each line at the correct position
                    for (line_idx, line) in lines.iter().enumerate() {
                        let y_offset = cursor_pos.row as u16 + line_idx as u16;
                        if y_offset >= editor_area.height {
                            break; // Don't render beyond editor area
                        }

                        let x_offset = if line_idx == 0 {
                            // First line starts from cursor position
                            cursor_pos.col as u16
                        } else {
                            // Subsequent lines start from column 0
                            0
                        };

                        let line_rect = ratatui::layout::Rect {
                            x: editor_area.x + x_offset,
                            y: editor_area.y + y_offset,
                            width: editor_area.width.saturating_sub(x_offset),
                            height: 1,
                        };

                        // Ensure we don't render outside the editor area
                        let line_area = editor_area.intersection(line_rect);
                        if line_area.width > 0 && line_area.height > 0 {
                            let line_paragraph = Paragraph::new(line.as_str())
                                .style(Style::default().fg(Color::DarkGray));
                            line_paragraph.render(line_area, buf);
                        }
                    }
                }
            }
        }

        // Render blocks
        message_block.render(messages_area, buf);
        user_block.render(user_area, buf);
    }
}

fn text_to_lines(text: &str, available_width: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut current_line = String::new();
    for ch in text.chars() {
        if ch == '\n' {
            lines.push(current_line.clone());
            current_line.clear();
        } else if current_line.len() >= available_width && !current_line.is_empty() {
            lines.push(current_line.clone());
            current_line.clear();
            current_line.push(ch);
        } else {
            current_line.push(ch);
        }
    }
    if !current_line.is_empty() {
        lines.push(current_line);
    }
    lines
}
