use derive_setters::Setters;
use ratatui::widgets::Widget;
use throbber_widgets_tui::ThrobberState;

#[derive(Clone, Default, Setters)]
pub struct Spinner {
    state: ThrobberState,
}

impl Spinner {
    pub fn on_tick(&mut self) {
        self.state.calc_next();
    }
}

impl Widget for Spinner {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        // Set full with state
        throbber_widgets_tui::Throbber::default()
            .label("Running...")
            .style(ratatui::style::Style::default().fg(ratatui::style::Color::Cyan))
            .throbber_style(
                ratatui::style::Style::default()
                    .fg(ratatui::style::Color::Red)
                    .add_modifier(ratatui::style::Modifier::BOLD),
            )
            .throbber_set(throbber_widgets_tui::CLOCK)
            .use_type(throbber_widgets_tui::WhichUse::Spin)
            .render(area, buf);
    }
}
