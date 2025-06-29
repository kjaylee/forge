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
