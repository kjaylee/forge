// Remove unused import and use ratatui's crossterm consistently
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent};
use ratatui::layout::{Alignment, Constraint, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::symbols::border::{PLAIN, Set};
use ratatui::symbols::line::NORMAL;
use ratatui::text::Line;
use ratatui::widgets::{Block, Borders, Padding, Paragraph, Widget};
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
                self.text_area.reset();
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
        let layout = Layout::vertical([Constraint::Fill(1), Constraint::Max(5)]);
        let [top_area, bottom_area] = layout.areas(area);
        let mut content_block = Block::bordered()
            .title(" Welcome to Forge ")
            .title_alignment(Alignment::Center)
            .border_set(Set {
                bottom_right: NORMAL.vertical_left,
                bottom_left: NORMAL.vertical_right,
                ..PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        let content = if self.state.messages.is_empty() {
            content_block = content_block.padding(Padding::new(0, 0, 4, 0));

            Paragraph::new(vec![
                "Use <CTRL+D> to exit".into(),
                "Use <CTRL+T> to toggle between PLAN & ACT mode".into(),
            ])
            .style(Style::default().dark_gray())
            .centered()
        } else {
            Paragraph::new(
                self.state
                    .messages
                    .iter()
                    .map(|msg| Line::from(msg.to_string()))
                    .collect::<Vec<_>>(),
            )
        };

        content.block(content_block).render(top_area, buf);

        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(Set {
                top_left: NORMAL.vertical_right,
                top_right: NORMAL.vertical_left,
                ..PLAIN
            })
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(self.state.mode.as_ref().to_string()));

        let area = user_block.inner(bottom_area);

        self.text_area.render(area, buf);
        user_block.render(bottom_area, buf);
    }
}
