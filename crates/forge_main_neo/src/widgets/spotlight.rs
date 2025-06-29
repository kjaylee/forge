use color_eyre::owo_colors::OwoColorize;
use edtui::{EditorTheme, EditorView};
use ratatui::layout::{Constraint, Flex, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Clear, Paragraph, StatefulWidget, Widget};

use crate::domain::State;

#[derive(Default)]
pub struct SpotlightWidget;

impl StatefulWidget for SpotlightWidget {
    type State = State;

    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut Self::State,
    ) {
        let [area] = Layout::vertical([Constraint::Percentage(75)])
            .flex(Flex::Center)
            .areas(area);

        let [area] = Layout::horizontal([Constraint::Percentage(80)])
            .flex(Flex::Center)
            .areas(area);

        Clear.render(area, buf);

        let [input_area, suggestion_area] =
            Layout::vertical([Constraint::Length(3), Constraint::Fill(0)]).areas(area);

        let input_block = Block::bordered()
            .title_style(Style::default().bold())
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().fg(Color::Blue))
            .title_top(" SPOTLIGHT ");

        EditorView::new(&mut state.spotlight.editor)
            .theme(
                EditorTheme::default()
                    .base(Style::reset())
                    .cursor_style(Style::default().fg(Color::Black).bg(Color::White))
                    .hide_status_line(),
            )
            .render(input_block.inner(input_area), buf);

        input_block.render(input_area, buf);

        let content_block = Block::bordered()
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().bold())
            .border_style(Style::default().fg(Color::Blue));
        let content = Paragraph::new("[Coming Soon]").block(content_block);

        content.render(suggestion_area, buf);
    }
}
