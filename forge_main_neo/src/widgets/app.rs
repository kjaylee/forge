// Remove unused import and use ratatui's crossterm consistently
use ratatui::crossterm::event::Event;
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Block, Widget};
use ratatui::{DefaultTerminal, Frame};

use super::state::State;
use super::status::StatusBar;
use super::text::ForgeTextArea;

#[derive(Debug)]
pub struct App {
    state: State,
    text_area: ForgeTextArea<'static>,
}

impl Default for App {
    fn default() -> Self {
        Self::new()
    }
}

impl App {
    pub fn new() -> Self {
        let text_area = ForgeTextArea::default();
        Self { state: State::default(), text_area }
    }

    pub fn run(&mut self, terminal: &mut DefaultTerminal) -> anyhow::Result<()> {
        while !self.state.exit {
            terminal.draw(|frame| self.draw(frame))?;
            if let Event::Key(key) = ratatui::crossterm::event::read()? {
                self.text_area.input(key);
                self.state.key_event(key)
            }
        }

        Ok(())
    }

    fn draw(&self, frame: &mut Frame) {
        frame.render_widget(self, frame.area());
    }
}

impl Widget for &App {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        let block = Block::bordered()
            .title_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(self.state.mode.as_ref().to_string()));

        let inner_area = block.inner(area);
        self.text_area.render(inner_area, buf);
        block.render(area, buf);
    }
}
