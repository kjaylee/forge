use color_eyre::owo_colors::OwoColorize;
use crossterm::event::{KeyCode, KeyModifiers};
use forge_api::ModelId;
use ratatui::crossterm::style::Color;
use ratatui::layout::{Alignment, Constraint, Flex, Layout, Rect};
use ratatui::style::{Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Block, Paragraph, Widget};
use ratatui::{DefaultTerminal, Frame};

#[derive(Debug, Default)]
pub struct App {
    state: State,
}

#[derive(Debug, Default)]
pub struct State {
    model_id: Option<ModelId>,
    exit: bool,
    suspend: bool,
}

impl App {
    pub fn run(&mut self, terminal: &mut DefaultTerminal) -> anyhow::Result<()> {
        while !self.state.exit {
            terminal.draw(|frame| self.draw(frame))?;
            if let crossterm::event::Event::Key(key_event) = crossterm::event::read()? {
                self.handle_key_event(key_event)
            }
        }
        Ok(())
    }

    fn handle_key_event(&mut self, key_event: crossterm::event::KeyEvent) {
        if let crossterm::event::KeyEvent {
            code: KeyCode::Char('d'),
            modifiers: KeyModifiers::CONTROL,
            ..
        } = key_event
        {
            self.state.exit = true
        }
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
        let instructions = Line::from(vec![" Exit ".into(), "<CTRL+D> ".into()])
            .bg(Color::DarkGrey)
            .fg(Color::Black)
            .bold();

        let block = Block::bordered()
            .title_style(Style::default().dark_gray())
            .title_bottom(instructions)
            .title_alignment(Alignment::Center);

        let area = block.inner(area);

        Paragraph::new("Hello Peeps")
            .block(block)
            .centered()
            .render(area, buf);
    }
}
