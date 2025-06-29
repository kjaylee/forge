use forge_api::ChatResponse;
use ratatui::style::{Color, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Paragraph, StatefulWidget, Widget, Wrap};

use crate::domain::{Message, State};
use crate::widgets::spinner::Spinner;

#[derive(Default)]
pub struct MessageList;

fn messages_to_lines(messages: &[Message]) -> Vec<Line<'_>> {
    messages
        .iter()
        .filter_map(|message| match message {
            Message::User(content) => Some(Line::from(vec![
                Span::styled("❯ ", Style::default().green()),
                Span::styled(content, Style::default().cyan().bold()),
            ])),
            Message::Assistant(response) => match response {
                ChatResponse::Text { text, is_complete, is_md: _, is_summary: _ } => {
                    if *is_complete {
                        Some(Line::raw(text))
                    } else {
                        None
                    }
                }
                ChatResponse::ToolCallStart(_) => None,
                ChatResponse::ToolCallEnd(_) => None,
                ChatResponse::Usage(_) => None,
            },
        })
        .collect()
}

impl StatefulWidget for MessageList {
    type State = State;
    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut State,
    ) where
        Self: Sized,
    {
        if state.messages.is_empty() {
            Paragraph::new(include_str!("./banner.txt"))
                .fg(Color::DarkGray)
                .centered()
                .wrap(Wrap { trim: false })
                .render(area, buf);
        } else {
            let mut lines = messages_to_lines(&state.messages);
            let s = Spinner::default();
            if state.show_spinner {
                lines.push(s.to_line(state));
            }
            Paragraph::new(lines)
                .wrap(Wrap { trim: false })
                .render(area, buf);
        };
    }
}
