use ratatui::crossterm::event::KeyEvent;
use ratatui::widgets::Widget;
use tui_textarea::TextArea;

#[derive(Debug, Default)]
pub struct ForgeTextArea<'a> {
    text_area: TextArea<'a>,
}

impl Widget for &ForgeTextArea<'_> {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        self.text_area.render(area, buf);
    }
}

impl ForgeTextArea<'_> {
    pub fn input(&mut self, key: KeyEvent) {
        self.text_area.input(key);
    }
}
