use forge_api::ChatResponse;
use ratatui::layout::{Alignment, Constraint, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::text::{Line, Span, Text};
use ratatui::widgets::{Paragraph, StatefulWidget, Widget, Wrap};

use crate::domain::{Message, State};
use crate::widgets::spinner::Spinner;

#[derive(Default)]
pub struct MessageList;

fn messages_to_lines(messages: &[Message]) -> Vec<Line<'_>> {
    messages
        .iter()
        .flat_map(|message| match message {
            Message::User(content) => vec![Line::from(vec![
                Span::styled("❯ ", Style::default().green()),
                Span::styled(content, Style::default().cyan().bold()),
            ])]
            .into_iter(),
            Message::Assistant(response) => match response {
                ChatResponse::Text { text, is_complete, is_md, is_summary: _ } => {
                    if *is_complete {
                        if *is_md {
                            // Use Text::from() which handles newlines automatically and more
                            // efficiently
                            let rendered_text = forge_display::MarkdownFormat::new().render(text);
                            Text::from(rendered_text).lines.into_iter()
                        } else {
                            vec![Line::raw(text.clone())].into_iter()
                        }
                    } else {
                        vec![].into_iter()
                    }
                }
                ChatResponse::ToolCallStart(_) => vec![].into_iter(),
                ChatResponse::ToolCallEnd(_) => vec![].into_iter(),
                ChatResponse::Usage(_) => vec![].into_iter(),
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
            let [top_layout, bottom_layout] =
                Layout::vertical([Constraint::Max(8), Constraint::Fill(1)]).areas(area);
            let [left_layout, right_layout] =
                Layout::horizontal([Constraint::Percentage(50), Constraint::Percentage(50)])
                    .areas(bottom_layout);

            // Create banner and welcome content for top section
            let mut banner_lines = Vec::new();

            // Add banner lines
            for line in include_str!("./banner.txt").lines() {
                banner_lines.push(Line::raw(line));
            }

            // Render banner and welcome message in top section
            Paragraph::new(banner_lines)
                .style(Style::new().fg(Color::Yellow))
                .centered()
                .wrap(Wrap { trim: false })
                .render(top_layout, buf);

            // Create keyboard shortcuts for bottom section
            let shortcuts = vec![
                ("CTRL+D", "Exit application"),
                ("TAB", "Navigate to next view"),
                ("SHIFT+TAB", "Navigate to previous view"),
                ("ENTER", "Submit message (in Chat mode)"),
                ("ESC", "Switch between modes"),
            ];

            // Create left column with right-aligned shortcuts
            let mut left_lines = Vec::new();
            for (shortcut, _) in &shortcuts {
                left_lines.push(
                    Line::from(vec![Span::styled(
                        format!("<{shortcut}> "),
                        Style::default().cyan(),
                    )])
                    .alignment(Alignment::Right),
                );
            }

            // Create right column with left-aligned descriptions
            let mut right_lines = Vec::new();
            for (_, description) in &shortcuts {
                right_lines.push(Line::from(vec![Span::styled(
                    *description,
                    Style::default().dim(),
                )]));
            }

            // Render shortcuts in two columns
            Paragraph::new(left_lines)
                .wrap(Wrap { trim: false })
                .render(left_layout, buf);

            Paragraph::new(right_lines)
                .wrap(Wrap { trim: false })
                .render(right_layout, buf);
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
