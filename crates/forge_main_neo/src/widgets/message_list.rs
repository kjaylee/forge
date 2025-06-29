use ratatui::layout::{Constraint, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Paragraph, StatefulWidget, Widget, Wrap};

use crate::domain::{Message, State};
use crate::widgets::spinner::Spinner;

#[derive(Default)]
pub struct MessageList;

fn messages_to_lines(messages: &Vec<Message>) -> Vec<Line<'_>> {
    messages
        .iter()
        .map(|message| match message {
            Message::User(content) => {
                Line::from(vec![Span::styled(content, Style::default().dim().bold())])
            }
            Message::Assistant(content) => Line::from(Span::raw(content)),
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
            let [message_area, loader_area] =
                Layout::vertical([Constraint::Fill(0), Constraint::Max(1)]).areas(area);

            Paragraph::new(messages_to_lines(&state.messages))
                .wrap(Wrap { trim: false })
                .render(message_area, buf);

            Spinner::default().render(loader_area, buf);
        };
    }
}
