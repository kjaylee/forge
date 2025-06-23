use ratatui::buffer::Buffer;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Padding, StatefulWidget, Widget};

use crate::model::State;
use crate::widgets::status_bar::StatusBar;

/// Container widget that provides a shared bordered layout with status bar
/// This widget wraps content and provides consistent styling across all routes
#[derive(Default)]
pub struct Container<W> {
    content: W,
    show_status_bar: bool,
}

impl<W> Container<W> {
    /// Create a new container with the given content widget
    pub fn new(content: W) -> Self {
        Self { content, show_status_bar: true }
    }

    /// Create a container without status bar
    pub fn without_status_bar(content: W) -> Self {
        Self { content, show_status_bar: false }
    }

    /// Set whether to show the status bar
    pub fn show_status_bar(mut self, show: bool) -> Self {
        self.show_status_bar = show;
        self
    }
}

impl<W> StatefulWidget for Container<W>
where
    W: StatefulWidget<State = State>,
{
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State)
    where
        Self: Sized,
    {
        if self.show_status_bar {
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
                .border_style(Style::default().dark_gray())
                .title_bottom(StatusBar::minimal(
                    state.current_branch.clone(),
                    state.current_dir.clone(),
                ));

            // Render the content inside the bordered area
            self.content
                .render(content_block.inner(content_area), buf, state);

            // Render the blocks
            content_block.render(content_area, buf);
            status_block.render(status_area, buf);
        } else {
            // Just render content with a simple border
            let content_block = Block::bordered()
                .border_style(Style::default().dark_gray())
                .title_style(Style::default().dark_gray());

            self.content.render(content_block.inner(area), buf, state);
            content_block.render(area, buf);
        }
    }
}

impl<W> Widget for Container<W>
where
    W: Widget,
{
    fn render(self, area: Rect, buf: &mut Buffer)
    where
        Self: Sized,
    {
        if self.show_status_bar {
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
                .border_style(Style::default().dark_gray())
                .title_bottom(StatusBar::minimal(None, None));

            // Render the content inside the bordered area
            self.content.render(content_block.inner(content_area), buf);

            // Render the blocks
            content_block.render(content_area, buf);
            status_block.render(status_area, buf);
        } else {
            // Just render content with a simple border
            let content_block = Block::bordered()
                .border_style(Style::default().dark_gray())
                .title_style(Style::default().dark_gray());

            self.content.render(content_block.inner(area), buf);
            content_block.render(area, buf);
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ratatui::widgets::Paragraph;

    use super::*;

    #[test]
    fn test_container_creation() {
        let content = Paragraph::new("Test content");
        let fixture = Container::new(content);
        let actual = fixture.show_status_bar;
        let expected = true;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_container_without_status_bar() {
        let content = Paragraph::new("Test content");
        let fixture = Container::without_status_bar(content);
        let actual = fixture.show_status_bar;
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_container_show_status_bar_toggle() {
        let content = Paragraph::new("Test content");
        let fixture = Container::new(content).show_status_bar(false);
        let actual = fixture.show_status_bar;
        let expected = false;
        assert_eq!(actual, expected);
    }
}
