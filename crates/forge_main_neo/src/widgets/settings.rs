use ratatui::buffer::Buffer;
use ratatui::prelude::Rect;
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Paragraph, Widget};

use crate::domain::{Action, Command};
use crate::widgets::bordered_panel::BorderedPanel;

/// Settings widget that handles the settings interface
#[derive(Clone)]
pub struct SettingsWidget {
    // Future settings-specific state can be added here
}

impl SettingsWidget {
    /// Create a new Settings widget
    pub fn new() -> Self {
        Self {
            // Future settings-specific state can be added here
        }
    }

    /// Handle events for the settings interface
    pub fn update(&mut self, _: impl Into<Action>) -> Command {
        // Settings view doesn't handle events yet
        Command::Empty
    }
}

impl Default for SettingsWidget {
    fn default() -> Self {
        Self::new()
    }
}

impl Widget for &SettingsWidget {
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
    use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, KeyModifiers};

    use super::*;

    #[test]
    fn test_settings_handle_event() {
        let mut fixture = SettingsWidget::new();

        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE);
        let actual = fixture.update(Event::Key(key_event));
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }
}
