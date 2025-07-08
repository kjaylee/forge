use color_eyre::owo_colors::OwoColorize;
use forge_api::ChatResponse;
use ratatui::layout::Size;
use ratatui::style::{Style, Stylize};
use ratatui::text::{Line, Span, Text};
use ratatui::widgets::{Paragraph, StatefulWidget, Wrap};
use tui_scrollview::ScrollView;

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
                ChatResponse::Text { text, is_complete, is_md } => {
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
                ChatResponse::Interrupt { reason: _ } => {
                    todo!()
                }
                ChatResponse::Reasoning { content } => {
                    if !content.trim().is_empty() {
                        Text::from(content.dimmed().to_string()).lines.into_iter()
                    } else {
                        vec![].into_iter()
                    }
                }
                ChatResponse::Summary { content } => {
                    if !content.trim().is_empty() {
                        let rendered_text = forge_display::MarkdownFormat::new().render(content);
                        Text::from(rendered_text).lines.into_iter()
                    } else {
                        vec![].into_iter()
                    }
                }
                ChatResponse::RetryAttempt { cause: _, duration: _ } => {
                    todo!()
                }
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
        let mut lines = messages_to_lines(&state.messages);
        let s = Spinner::default();
        if state.show_spinner {
            lines.push(s.to_line(state));
        }

        // Create the scroll view
        let mut scroll_view = ScrollView::new(Size::new(area.width, area.height))
            .horizontal_scrollbar_visibility(tui_scrollview::ScrollbarVisibility::Never);

        // Render the paragraph into the scroll view's buffer
        let paragraph = Paragraph::new(lines).wrap(Wrap { trim: false });
        scroll_view.render_widget(paragraph, scroll_view.area());

        // Render the scroll view into the main buffer
        scroll_view.render(area, buf, &mut state.message_scroll_state);
    }
}
