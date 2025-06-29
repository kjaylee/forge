use derive_setters::Setters;
use ratatui::buffer::Buffer;
use ratatui::crossterm::event::{Event, KeyCode, KeyModifiers};
use ratatui::prelude::Rect;
use ratatui::widgets::Widget;

use crate::action::Action;
use crate::command::Command;
use crate::widgets::chat::Chat;
use crate::widgets::help::Help;
use crate::widgets::settings::Settings;

/// Router widget that renders different content based on the current route
#[derive(Clone, Default, Setters)]
#[setters(strip_option, into)]
pub struct Router {
    pub current_route: Route,
    pub chat: Chat,
    pub settings: Settings,
    pub help: Help,
}

impl Router {
    /// Navigate to the next route
    pub fn navigate_next(&mut self) {
        self.current_route = self.current_route.next();
    }

    /// Navigate to the previous route
    pub fn navigate_previous(&mut self) {
        self.current_route = self.current_route.previous();
    }

    /// Handle events for the current route
    pub fn update(&mut self, action: impl Into<Action>) -> Command {
        let action = action.into();
        match &action {
            Action::CrossTerm(Event::Key(key_event)) => {
                let shift = key_event.modifiers.contains(KeyModifiers::SHIFT);

                // Navigation shortcuts
                if key_event.code == KeyCode::Tab && !shift {
                    self.navigate_next();
                    self.current_route = self.current_route.clone();
                    return Command::Empty;
                }

                if key_event.code == KeyCode::BackTab || (key_event.code == KeyCode::Tab && shift) {
                    self.navigate_previous();
                    self.current_route = self.current_route.clone();
                    return Command::Empty;
                }

                self.handle_route(action)
            }
            _ => self.handle_route(action),
        }
    }

    fn handle_route(&mut self, action: impl Into<Action>) -> Command {
        match self.current_route {
            Route::Chat => self.chat.update(action),
            Route::Settings => self.settings.update(action),
            Route::Help => self.help.update(action),
        }
    }
}

/// Represents the different routes/views available in the application
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum Route {
    #[default]
    Chat,
    Settings,
    Help,
}

impl Route {
    /// Get all available routes
    pub fn all() -> Vec<Route> {
        vec![Route::Chat, Route::Settings, Route::Help]
    }

    /// Get the display name for the route
    pub fn display_name(&self) -> &'static str {
        match self {
            Route::Chat => "CHAT",
            Route::Settings => "SETTINGS",
            Route::Help => "HELP",
        }
    }

    /// Navigate to the next route in sequence
    pub fn next(&self) -> Route {
        match self {
            Route::Chat => Route::Settings,
            Route::Settings => Route::Help,
            Route::Help => Route::Chat,
        }
    }

    /// Navigate to the previous route in sequence
    pub fn previous(&self) -> Route {
        match self {
            Route::Chat => Route::Help,
            Route::Settings => Route::Chat,
            Route::Help => Route::Settings,
        }
    }
}

impl Widget for Router {
    fn render(self, area: Rect, buf: &mut Buffer)
    where
        Self: Sized,
    {
        match self.current_route {
            Route::Chat => {
                // Render the chat widget
                self.chat.render(area, buf);
            }
            Route::Settings => {
                // Render the settings widget
                self.settings.render(area, buf);
            }
            Route::Help => {
                // Render the help widget
                self.help.render(area, buf);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_route_navigation() {
        let fixture = Route::Chat;
        let actual = fixture.next();
        let expected = Route::Settings;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_route_previous_navigation() {
        let fixture = Route::Settings;
        let actual = fixture.previous();
        let expected = Route::Chat;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_route_display_names() {
        let fixture = Route::Chat;
        let actual = fixture.display_name();
        let expected = "CHAT";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_creation() {
        let fixture = Router::default();
        let actual = fixture.current_route;
        let expected = Route::Chat;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_next_navigation() {
        let mut fixture = Router::default();
        fixture.navigate_next();
        let actual = fixture.current_route;
        let expected = Route::Settings;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_previous_navigation() {
        let mut fixture = Router::default().current_route(Route::Settings);
        fixture.navigate_previous();
        let actual = fixture.current_route;
        let expected = Route::Chat;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_route_cycle() {
        let fixture = Route::Help;
        let actual = fixture.next();
        let expected = Route::Chat;
        assert_eq!(actual, expected);
    }
}
