use ratatui::{
    layout::{Constraint, Direction, Layout},
    style::{Color, Style},
    widgets::{Block, Borders, Widget},
};

#[derive(Default)]
pub struct App {}

impl Widget for &App {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        let main_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(4)],
        );
        let [top, bottom] = main_layout.areas(area);

        let block = Block::new().title(" Hello World ").borders(Borders::all());
        block.render(bottom, buf);
    }
}
