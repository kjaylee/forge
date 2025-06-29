use chrono::Duration;
use ratatui::widgets::StatefulWidget;

use crate::domain::State;

#[derive(Clone, Default)]
pub struct Spinner {}

impl Spinner {}

impl StatefulWidget for Spinner {
    type State = State;
    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut State,
    ) where
        Self: Sized,
    {
        let duration = state
            .timer
            .as_ref()
            .map(|timer| {
                Duration::milliseconds(
                    timer.current_time.timestamp_millis() - timer.start_time.timestamp_millis(),
                )
                .num_seconds()
            })
            .unwrap_or_default();
        // Set full with state
        let th = throbber_widgets_tui::Throbber::default()
            .label(format!("Running... {}", duration))
            .style(ratatui::style::Style::default().fg(ratatui::style::Color::Cyan))
            .throbber_style(
                ratatui::style::Style::default()
                    .fg(ratatui::style::Color::Red)
                    .add_modifier(ratatui::style::Modifier::BOLD),
            )
            .throbber_set(throbber_widgets_tui::CLOCK)
            .use_type(throbber_widgets_tui::WhichUse::Spin);

        StatefulWidget::render(th, area, buf, &mut state.spinner);
    }
}
