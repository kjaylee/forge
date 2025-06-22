use derive_setters::Setters;
use ratatui::text::Line;
use ratatui::widgets::{Paragraph, Widget, Wrap};

use crate::widgets::welcome::Welcome;

#[derive(Default, Setters)]
pub struct MessageList {
    pub messages: Vec<String>,
}

impl Widget for MessageList {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        if self.messages.is_empty() {
            Welcome::default().render(area, buf);
        } else {
            Paragraph::new(self.messages.iter().map(Line::raw).collect::<Vec<_>>())
                .wrap(Wrap { trim: false })
                .render(area, buf);
        };
    }
}
