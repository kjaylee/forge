// use anyhow::Context;
use std::sync::mpsc;

use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, MouseEvent, MouseEventKind};
use ratatui::layout::{Alignment, Constraint, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::symbols::border::{self};
use ratatui::symbols::line::{self};
use ratatui::symbols::{scrollbar, shade};
use ratatui::text::Line;
use ratatui::widgets::{
    Block, Borders, Padding, Paragraph, Scrollbar, ScrollbarOrientation, ScrollbarState,
    StatefulWidget, Widget,
};
use ratatui::{DefaultTerminal, Frame};

use super::input::ForgeInput;
use super::status::StatusBar;
use crate::domain::{Message, State};

#[derive(Debug)]
pub struct App {
    state: State,
    user_text_area: ForgeInput<'static>,
    scroll_state: ScrollbarState,
    content_position: usize,
}

impl App {
    pub fn new() -> Self {
        Self {
            state: State::default(),
            user_text_area: ForgeInput::default(),
            scroll_state: ScrollbarState::default(),
            content_position: 0,
        }
    }

    pub fn run(
        &mut self,
        terminal: &mut DefaultTerminal,
        rx: mpsc::Receiver<Message>,
    ) -> anyhow::Result<()> {
        while !self.state.exit {
            terminal.draw(|frame| self.draw(frame))?;
            let event = rx.recv()?;
            match event {
                Message::KeyBoard(Event::Key(key)) => self.key_event(key),
                Message::KeyBoard(Event::Mouse(mouse)) => self.mouse_event(mouse),
                _ => {}
            }
        }

        Ok(())
    }

    fn mouse_event(&mut self, mouse: MouseEvent) {
        match mouse.kind {
            MouseEventKind::ScrollDown => {
                let max_position = self.state.messages.len().saturating_sub(1);
                if self.content_position < max_position {
                    self.content_position = self.content_position.saturating_add(1);
                }
            }
            MouseEventKind::ScrollUp => {
                if self.content_position > 0 {
                    self.content_position = self.content_position.saturating_sub(1);
                }
            }
            _ => {}
        }
    }

    fn key_event(&mut self, key: KeyEvent) {
        match (key.code, key.modifiers) {
            (KeyCode::Enter, _) => {
                let lines = self.user_text_area.text();
                if lines.iter().any(|line| !line.is_empty()) {
                    self.state.messages.extend(
                        lines
                            .iter()
                            .map(|line| line.trim().to_string())
                            .filter(|line| !line.is_empty()),
                    );
                    self.user_text_area.reset();
                }
            }
            _ => {
                self.user_text_area.input(key);
            }
        }
        self.state.key_event(key)
    }

    fn draw(&mut self, frame: &mut Frame) {
        frame.render_widget(self, frame.area());
    }
}

impl Widget for &mut App {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        let layout = Layout::vertical([Constraint::Fill(1), Constraint::Max(5)]);
        let [top_area, bottom_area] = layout.areas(area);
        let mut content_block = Block::bordered()
            .title(" Welcome to Forge ")
            .title_alignment(Alignment::Center)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        let content = if self.state.messages.is_empty() {
            // Getting Started Section
            content_block = content_block.padding(Padding::new(0, 0, 4, 0));

            Paragraph::new(vec![
                "Use <CTRL+D> to exit".into(),
                "Use <CTRL+T> to toggle between PLAN & ACT mode".into(),
            ])
            .style(Style::default().dark_gray())
            .centered()
        } else {
            // Chat Started Section

            Paragraph::new(
                self.state
                    .messages
                    .iter()
                    .map(|msg| Line::from(msg.to_string()))
                    .collect::<Vec<_>>(),
            )
            .scroll((self.content_position as u16, 0))
        };

        content.block(content_block).render(top_area, buf);

        let content_length = self.state.messages.len().max(1);
        self.scroll_state = ScrollbarState::new(content_length).position(self.content_position);

        Scrollbar::new(ScrollbarOrientation::VerticalRight)
            .symbols(scrollbar::Set {
                track: line::VERTICAL,
                thumb: shade::MEDIUM,
                end: line::VERTICAL_LEFT,
                begin: line::TOP_RIGHT,
            })
            .render(top_area, buf, &mut self.scroll_state);

        let user_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray())
            .title_bottom(StatusBar::new(self.state.mode.as_ref().to_string()));

        let area = user_block.inner(bottom_area);

        self.user_text_area.render(area, buf);
        user_block.render(bottom_area, buf);
    }
}
