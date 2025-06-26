use ratatui::buffer::Buffer;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Padding, StatefulWidget, Widget};

use crate::model::State;

/// Container widget that provides a shared bordered layout with status bar
/// This widget wraps content and provides consistent styling across all routes
#[derive(Default)]
pub struct ChatContainer<W> {
    content: W,
}

impl<W> ChatContainer<W> {
    /// Crete a new container with the given content widget
    pub fn new(content: W) -> Self {
        Self { content }
    }
}

impl<W> StatefulWidget for ChatContainer<W>
where
    W: StatefulWidget<State = State>,
{
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State)
    where
        Self: Sized,
    {
        // Create layout with content area and status bar area
        let layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(3)],
        );
        let [content_area, status_area] = layout.areas(area);

        // Render content block
        let content_block = Block::bordered()
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT | Borders::TOP)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        // Render status bar block
        let status_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray());

        // Render the content inside the bordered area
        self.content
            .render(content_block.inner(content_area), buf, state);

        // Render the blocks
        content_block.render(content_area, buf);
        status_block.render(status_area, buf);
    }
}

impl<W> Widget for ChatContainer<W>
where
    W: Widget,
{
    fn render(self, area: Rect, buf: &mut Buffer)
    where
        Self: Sized,
    {
        // Create layout with content area and status bar area
        let layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(3)],
        );
        let [content_area, status_area] = layout.areas(area);

        // Render content block
        let content_block = Block::bordered()
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT | Borders::TOP)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        // Render status bar block (without state-dependent info)
        let status_block = Block::bordered()
            .padding(Padding::new(0, 0, 0, 1))
            .border_set(border::Set {
                top_left: line::VERTICAL_RIGHT,
                top_right: line::VERTICAL_LEFT,
                ..border::PLAIN
            })
            .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
            .title_style(Style::default().dark_gray())
            .border_style(Style::default().dark_gray());

        // Render the content inside the bordered area
        self.content.render(content_block.inner(content_area), buf);

        // Render the blocks
        content_block.render(content_area, buf);
        status_block.render(status_area, buf);
    }
}
