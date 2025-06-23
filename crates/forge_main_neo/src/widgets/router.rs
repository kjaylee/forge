use ratatui::buffer::Buffer;
use ratatui::prelude::Rect;
use ratatui::widgets::{StatefulWidget, Widget};

use crate::model::State;
use crate::widgets::message_list::MessageList;

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

/// Router widget that renders different content based on the current route
#[derive(Default)]
pub struct Router {
    current_route: Route,
}

impl Router {
    /// Create a new router with the default route
    pub fn new() -> Self {
        Self { current_route: Route::default() }
    }

    /// Create a router with a specific initial route
    pub fn with_route(route: Route) -> Self {
        Self { current_route: route }
    }

    /// Get the current route
    pub fn current_route(&self) -> &Route {
        &self.current_route
    }

    /// Navigate to a specific route
    pub fn navigate_to(&mut self, route: Route) {
        self.current_route = route;
    }

    /// Navigate to the next route
    pub fn navigate_next(&mut self) {
        self.current_route = self.current_route.next();
    }

    /// Navigate to the previous route
    pub fn navigate_previous(&mut self) {
        self.current_route = self.current_route.previous();
    }
}

impl StatefulWidget for &Router {
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State)
    where
        Self: Sized,
    {
        match self.current_route {
            Route::Chat => {
                // For now, render the message list - this can be expanded later
                MessageList::default()
                    .messages(state.messages.clone())
                    .render(area, buf);
            }
            Route::Settings => {
                // Placeholder for settings view
                use ratatui::style::{Style, Stylize};
                use ratatui::widgets::Paragraph;

                Paragraph::new("Settings View - Coming Soon!")
                    .style(Style::default().yellow())
                    .centered()
                    .render(area, buf);
            }
            Route::Help => {
                // Combined Welcome and Help view
                use ratatui::style::{Style, Stylize};
                use ratatui::widgets::Paragraph;

                Paragraph::new(vec![
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
                .centered()
                .render(area, buf);
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
        let expected = "  Chat  ";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_creation() {
        let fixture = Router::new();
        let actual = fixture.current_route();
        let expected = &Route::Chat;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_navigation() {
        let mut fixture = Router::new();
        fixture.navigate_to(Route::Settings);
        let actual = fixture.current_route();
        let expected = &Route::Settings;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_next_navigation() {
        let mut fixture = Router::new();
        fixture.navigate_next();
        let actual = fixture.current_route();
        let expected = &Route::Settings;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_previous_navigation() {
        let mut fixture = Router::with_route(Route::Settings);
        fixture.navigate_previous();
        let actual = fixture.current_route();
        let expected = &Route::Chat;
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
