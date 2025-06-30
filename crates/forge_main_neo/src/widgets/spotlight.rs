use edtui::{EditorTheme, EditorView};
use ratatui::layout::{Constraint, Flex, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Clear, List, ListItem, StatefulWidget, Widget};

use crate::domain::State;

fn get_spotlight_input_text(editor: &edtui::EditorState) -> String {
    editor
        .lines
        .iter_row()
        .map(|row| row.iter().collect::<String>())
        .collect::<Vec<_>>()
        .join("\n")
        .to_lowercase()
}

#[derive(Default)]
pub struct SpotlightWidget;

impl SpotlightWidget {}

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

        let [input_area, content_area] =
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

        // Get the current input text for filtering
        let input_text = get_spotlight_input_text(&state.spotlight.editor);

        // Filter commands that start with the input text
        let filtered_commands: Vec<&(String, String)> = state
            .spotlight
            .commands
            .iter()
            .filter(|(name, _)| name.to_lowercase().starts_with(&input_text))
            .collect();

        // Calculate the maximum width of filtered command names for consistent
        // alignment
        let max_name_width = filtered_commands
            .iter()
            .map(|(name, _)| name.len())
            .max()
            .unwrap_or(0);

        // Create list items with padded command names for aligned descriptions
        let items: Vec<ListItem> = filtered_commands
            .iter()
            .enumerate()
            .map(|(i, (name, desc))| {
                let style = if i == state.spotlight.selected_index {
                    Style::default().bg(Color::White).fg(Color::Black)
                } else {
                    Style::default()
                };

                // Pad the name to the maximum width and add a separator
                let padded_name = format!("{name:<max_name_width$} ");

                let line = Line::from(vec![
                    Span::styled(padded_name, Style::default().bold().fg(Color::Cyan)),
                    Span::styled(desc, Style::default().fg(Color::Green)),
                ]);

                ListItem::new(line).style(style)
            })
            .collect();

        let commands_list = List::new(items).block(
            Block::bordered()
                .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
                .border_style(Style::default().fg(Color::Blue)),
        );

        Widget::render(commands_list, content_area, buf);
    }
}
