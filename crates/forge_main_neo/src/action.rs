use derive_more::From;
use ratatui::crossterm::event::Event;

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

/// Chat-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum ChatAction {
    MessageAdded(String),
}

/// Router-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum RouterAction {
    NavigateToRoute(Route),
    
}

/// Help-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum HelpAction {
    // Future help actions can be added here
}

/// Settings-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum SettingsAction {
    // Future settings actions can be added here
}

/// Top-level application actions that wrap route-specific actions
#[derive(From, Debug, Clone, PartialEq)]
pub enum Action {
    CrossTerm(Event),
    Initialize,
    Workspace {
        current_dir: Option<String>,
        current_branch: Option<String>,
    },
    ChatResponse {
        message: String,
    },
    // Route-specific action containers
    Router(RouterAction),
    Chat(ChatAction),
    Help(HelpAction),
    Settings(SettingsAction),
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
    fn test_route_cycle() {
        let fixture = Route::Help;
        let actual = fixture.next();
        let expected = Route::Chat;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_chat_action_message_added() {
        let fixture = ChatAction::MessageAdded("test".to_string());
        let actual = fixture;
        let expected = ChatAction::MessageAdded("test".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_router_action_navigate_to_route() {
        let fixture = RouterAction::NavigateToRoute(Route::Settings);
        let actual = fixture;
        let expected = RouterAction::NavigateToRoute(Route::Settings);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_action_workspace() {
        let fixture = Action::Workspace {
            current_dir: Some("test".to_string()),
            current_branch: Some("main".to_string()),
        };
        let actual = fixture;
        let expected = Action::Workspace {
            current_dir: Some("test".to_string()),
            current_branch: Some("main".to_string()),
        };
        assert_eq!(actual, expected);
    }
}
