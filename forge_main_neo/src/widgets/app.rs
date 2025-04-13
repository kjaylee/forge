// Remove unused import and use ratatui's crossterm consistently
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent};
use ratatui::layout::{Constraint, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Block, Padding, Paragraph, Widget};
use ratatui::{DefaultTerminal, Frame};

use super::state::State;
use super::status::StatusBar;
use super::text::ForgeInput;

#[derive(Debug)]
pub struct App {
    state: State,
    text_area: ForgeInput<'static>,
}

impl Default for App {
    fn default() -> Self {
        Self::new()
    }
}

impl App {
    pub fn new() -> Self {
        let text_area = ForgeInput::default();
        Self { state: State::default(), text_area }
    }

    pub fn run(&mut self, terminal: &mut DefaultTerminal) -> anyhow::Result<()> {
        while !self.state.exit {
            terminal.draw(|frame| self.draw(frame))?;
            if let Event::Key(key) = ratatui::crossterm::event::read()? {
                self.handle_event(key);
            }
        }

        Ok(())
    }

    fn handle_event(&mut self, key: KeyEvent) {
        match (key.code, key.modifiers) {
            (KeyCode::Enter, _) => {
                self.state
                    .messages
                    .extend(self.text_area.text().iter().cloned());
                self.text_area.clear();
            }
            _ => {
                self.text_area.input(key);
            }
        }
        self.state.key_event(key)
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
        let layout = Layout::vertical([Constraint::Percentage(100), Constraint::Min(4)]);
        let [top_area, bottom_area] = layout.areas(area);

        let paragraph = Paragraph::new(self.state.messages.join("\n"));
        paragraph.render(top_area, buf);

        let block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .title_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(self.state.mode.as_ref().to_string()));

        let area = block.inner(bottom_area);

        self.text_area.render(area, buf);
        block.render(bottom_area, buf);
    }
}
