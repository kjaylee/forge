use ratatui::buffer::Buffer;
use ratatui::crossterm::event::Event;
use ratatui::prelude::Rect;
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Paragraph, Widget};

use crate::model::Command;
use crate::widgets::bordered_panel::BorderedPanel;

/// Settings widget that handles the settings interface
#[derive(Default)]
pub struct Settings {}

impl Settings {
    /// Create a new Settings widget
    pub fn new() -> Self {
        Self {}
    }

    /// Handle events for the settings interface
    pub fn handle_event(&mut self, _event: Event) -> Command {
        // Settings view doesn't handle events yet
        Command::Empty
    }
}

impl Widget for &Settings {
    fn render(self, area: Rect, buf: &mut Buffer)
    where
        Self: Sized,
    {
        let content = Paragraph::new("Settings View - Coming Soon!")
            .style(Style::default().yellow())
            .centered();

        let panel = BorderedPanel::new(content);
        Widget::render(panel, area, buf);
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ratatui::crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    use super::*;

    #[test]
    fn test_settings_creation() {
        let _fixture = Settings::new();
        assert!(true); // Settings creation successful if we reach this point
    }

    #[test]
    fn test_settings_handle_event() {
        let mut fixture = Settings::new();

        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE);
        let actual = fixture.handle_event(Event::Key(key_event));
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }
}
