use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{StatefulWidget, Tabs, Widget};

use crate::domain::{Route, State};
use crate::widgets::RouterWidget;

#[derive(Clone, Default)]
pub struct App;

impl StatefulWidget for App {
    type State = State;
    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut State,
    ) where
        Self: Sized,
    {
        // Create main layout with tabs at the top
        let main_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Max(1), Constraint::Fill(0)],
        );
        let [tabs_area, content_area] = main_layout.areas(area);

        // Render tabs
        let tab_titles: Vec<Line> = Route::all()
            .iter()
            .map(|route| Line::from(route.display_name()))
            .collect();

        let current_tab_index = Route::all()
            .iter()
            .position(|route| route == &state.current_route)
            .unwrap_or(0);

        Tabs::new(tab_titles)
            .style(Style::default().dark_gray())
            .highlight_style(Style::default().yellow().bold())
            .select(current_tab_index)
            .divider(" ")
            .render(tabs_area, buf);

        // Delegate content rendering to router with shared state
        RouterWidget.render(content_area, buf, state);
    }
}
