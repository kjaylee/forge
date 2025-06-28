use ratatui::style::{Color, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Paragraph, Widget, Wrap};

#[derive(Default)]
pub struct MessageList {
    pub messages: Vec<String>,
}

impl MessageList {
    pub fn new(messages: Vec<String>) -> Self {
        Self { messages }
    }
}

impl Widget for MessageList {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        if self.messages.is_empty() {
            Paragraph::new(include_str!("./banner.txt"))
                .fg(Color::DarkGray)
                .centered()
                .wrap(Wrap { trim: false })
                .render(area, buf);
        } else {
            Paragraph::new(self.messages.iter().map(Line::raw).collect::<Vec<_>>())
                .wrap(Wrap { trim: false })
                .render(area, buf);
        };
    }
}
