use ratatui::buffer::Buffer;
use ratatui::layout::Rect;
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Block, Borders, StatefulWidget, Widget};

use crate::model::State;

/// A reusable bordered panel that wraps content with consistent styling
/// This provides a simple border around any widget content for visual
/// consistency
#[derive(Default)]
pub struct BorderedPanel<W> {
    content: W,
    title: Option<String>,
}

impl<W> BorderedPanel<W> {
    /// Create a new bordered panel with the given content widget
    pub fn new(content: W) -> Self {
        Self { content, title: None }
    }

    /// Set the title for the bordered panel
    pub fn title<T: Into<String>>(mut self, title: T) -> Self {
        self.title = Some(title.into());
        self
    }
}

impl<W> StatefulWidget for BorderedPanel<W>
where
    W: StatefulWidget<State = State>,
{
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State)
    where
        Self: Sized,
    {
        // Create a bordered block
        let mut block = Block::bordered()
            .borders(Borders::ALL)
            .border_style(Style::default().dark_gray());

        // Add title if provided
        if let Some(title) = self.title {
            block = block.title(title).title_style(Style::default().cyan());
        }

        // Render the content inside the bordered area
        self.content.render(block.inner(area), buf, state);

        // Render the border
        block.render(area, buf);
    }
}

impl<W> Widget for BorderedPanel<W>
where
    W: Widget,
{
    fn render(self, area: Rect, buf: &mut Buffer)
    where
        Self: Sized,
    {
        // Create a bordered block
        let mut block = Block::bordered()
            .borders(Borders::ALL)
            .border_style(Style::default().dark_gray());

        // Add title if provided
        if let Some(title) = self.title {
            block = block.title(title).title_style(Style::default().cyan());
        }

        // Render the content inside the bordered area
        self.content.render(block.inner(area), buf);

        // Render the border
        block.render(area, buf);
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ratatui::widgets::Paragraph;

    use super::*;

    #[test]
    fn test_bordered_panel_creation() {
        let content = Paragraph::new("Test content");
        let _fixture = BorderedPanel::new(content);
        assert!(true); // BorderedPanel creation successful if we reach this point
    }

    #[test]
    fn test_bordered_panel_with_title() {
        let content = Paragraph::new("Test content");
        let panel = BorderedPanel::new(content).title("Test Title");
        let actual = panel.title.as_ref().unwrap();
        let expected = "Test Title";
        assert_eq!(actual, expected);
    }
}
