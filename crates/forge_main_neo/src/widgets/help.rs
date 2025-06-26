use ratatui::buffer::Buffer;
use ratatui::crossterm::event::Event;
use ratatui::prelude::Rect;
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Paragraph, StatefulWidget, Widget};

use crate::model::{Command, State};
use crate::widgets::bordered_panel::BorderedPanel;

/// Help widget that handles the help interface
#[derive(Default)]
pub struct Help;

impl Help {
    /// Create a new Help widget
    pub fn new() -> Self {
        Self
    }

    /// Handle events for the help interface
    pub fn handle_event(&mut self, _event: Event, _state: &mut State) -> Command {
        // Help view doesn't handle events yet
        Command::Empty
    }
}

impl StatefulWidget for &Help {
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, _state: &mut Self::State)
    where
        Self: Sized,
    {
        let content = Paragraph::new(vec![
            "Welcome to Forge!".into(),
            "".into(),
            "Forge is an AI-powered development assistant that helps you".into(),
            "build, debug, and enhance your code projects.".into(),
            "".into(),
            "Keyboard Shortcuts:".into(),
            "".into(),
            "<CTRL+D> - Exit application".into(),
            "<TAB> - Navigate to next view".into(),
            "<SHIFT+TAB> - Navigate to previous view".into(),
            "<ENTER> - Submit message (in Chat mode)".into(),
        ])
        .style(Style::default().cyan())
        .centered();

        let panel = BorderedPanel::new(content).title("Help");
        Widget::render(panel, area, buf);
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ratatui::crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    use super::*;

    fn create_test_state() -> State {
        State::default()
    }

    #[test]
    fn test_help_creation() {
        let _fixture = Help::new();
        assert!(true); // Help creation successful if we reach this point
    }

    #[test]
    fn test_help_handle_event() {
        let mut fixture = Help::new();
        let mut state = create_test_state();

        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE);
        let actual = fixture.handle_event(Event::Key(key_event), &mut state);
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }
}
