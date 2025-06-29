use ratatui::buffer::Buffer;
use ratatui::prelude::Rect;
use ratatui::widgets::{StatefulWidget, Widget};

use crate::domain::{Route, State};
use crate::widgets::chat::ChatWidget;
use crate::widgets::help::HelpWidget;
use crate::widgets::settings::SettingsWidget;

/// Router widget that renders different content based on the current route
#[derive(Clone, Default)]
pub struct RouterWidget;

impl StatefulWidget for RouterWidget {
    type State = State;
    fn render(self, area: Rect, buf: &mut Buffer, state: &mut State)
    where
        Self: Sized,
    {
        match state.current_route {
            Route::Chat => {
                // Render the chat widget
                ChatWidget::default().render(area, buf, state);
            }
            Route::Settings => {
                // Render the settings widget
                SettingsWidget::default().render(area, buf);
            }
            Route::Help => {
                // Render the help widget
                HelpWidget::default().render(area, buf);
            }
        }
    }
}
