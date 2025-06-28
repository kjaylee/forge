use derive_setters::Setters;
use ratatui::buffer::Buffer;
use ratatui::prelude::Rect;
use ratatui::widgets::Widget;

use crate::action::Route;
use crate::command::Command as Command;
use crate::widgets::chat::Chat;
use crate::widgets::help::Help;
use crate::widgets::settings::Settings;

/// Router widget that renders different content based on the current route
#[allow(clippy::needless_update)]
#[derive(Clone, Default, Setters)]
#[setters(strip_option, into)]
pub struct Router {
    pub current_route: Route,
    pub chat: Chat,
    pub settings: Settings,
    pub help: Help,
}

impl Router {
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

    /// Handle events for the current route
    pub fn update(&mut self, event: ratatui::crossterm::event::Event) -> Command {
        match self.current_route {
            Route::Chat => {
                // Get chat command and convert to router command if needed
                let _chat_cmd = self.chat.handle_event(event);
                // For now, router just returns empty for chat commands
                // In the future, we might need to wrap or translate these
                Command::Empty
            }
            Route::Settings => {
                self.settings.handle_event(event);
                Command::Empty
            }
            Route::Help => {
                let _help_cmd = self.help.handle_event(event);
                Command::Empty
            }
        }
    }
}

impl Router {
    /// Add a message to the chat widget (assumes assistant message for
    /// ChatResponse)
    pub fn add_chat_message(&mut self, message: String) {
        self.chat.add_assistant_message(message);
    }

    /// Add a user message to the chat widget
    pub fn add_user_chat_message(&mut self, message: String) {
        self.chat.add_user_message(message);
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
    fn test_router_navigation() {
        let mut fixture = Router::default();
        fixture.navigate_to(Route::Settings);
        let actual = fixture.current_route;
        let expected = Route::Settings;
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
