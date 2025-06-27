use std::any::{Any, TypeId};

use derive_more::From;

/// Help-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum Action {
    // Future help actions can be added here
}

/// Help-specific commands
#[derive(Clone, From, PartialEq, Eq, Debug)]
pub enum Command {
    Empty,
    And(Vec<Command>),
    Tagged(Box<Command>, TypeId),
}

impl Command {
    pub fn and(self, other: Command) -> Command {
        match self {
            Command::And(mut commands) => {
                commands.push(other);
                Command::And(commands)
            }
            _ => Command::And(vec![self, other]),
        }
    }

    pub fn tagged<T: Any>(self, t: T) -> Self {
        Command::Tagged(Box::new(self), t.type_id())
    }
}
#[derive(Default, derive_setters::Setters)]
#[setters(strip_option, into)]
pub struct State {
    // Future help-specific state can be added here
}

use ratatui::buffer::Buffer;
use ratatui::crossterm::event::Event;
use ratatui::prelude::Rect;
use ratatui::style::{Style, Stylize};
use ratatui::widgets::{Paragraph, Widget};

use crate::widgets::bordered_panel::BorderedPanel;

/// Help widget that handles the help interface
pub struct Help {
    state: State,
}

impl Help {
    /// Create a new Help widget
    pub fn new() -> Self {
        Self { state: State::default() }
    }

    /// Handle events for the help interface
    pub fn handle_event(&mut self, _event: Event) -> Command {
        // Help view doesn't handle events yet
        Command::Empty
    }
}

impl Default for Help {
    fn default() -> Self {
        Self::new()
    }
}

impl Widget for &Help {
    fn render(self, area: Rect, buf: &mut Buffer)
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

        BorderedPanel::new(content).render(area, buf);
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use ratatui::crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    use super::*;

    #[test]
    fn test_help_creation() {
        let _fixture = Help::new();
        assert!(true); // Help creation successful if we reach this point
    }

    #[test]
    fn test_help_handle_event() {
        let mut fixture = Help::new();

        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE);
        let actual = fixture.handle_event(Event::Key(key_event));
        let expected = Command::Empty;
        assert_eq!(actual, expected);
    }
}
