use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Block, Padding, Paragraph, Widget};

#[derive(Default)]
pub struct Welcome {}

impl Widget for Welcome {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        Paragraph::new(vec![
            "Use <CTRL+D> to exit".into(),
            "Use <CTRL+T> to toggle between PLAN & ACT mode".into(),
        ])
        .style(Style::default().dark_gray())
        .centered()
        .block(Block::new().padding(Padding::new(0, 0, 4, 0)))
        .render(area, buf);
    }
}
