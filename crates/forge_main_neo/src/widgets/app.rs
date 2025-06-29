use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Tabs, Widget};

use crate::action::Action;
use crate::command::Command;
use crate::widgets::Router;
use crate::widgets::router::Route;

#[derive(Clone, Default, derive_setters::Setters)]
#[setters(strip_option, into)]
pub struct App {
    router: Router,
    pub current_branch: Option<String>,
    pub current_dir: Option<String>,
}

impl App {
    #[must_use]
    pub fn update(&mut self, action: impl Into<Action>) -> Command {
        let action = action.into();
        match &action {
            Action::Initialize => Command::ReadWorkspace,
            Action::Workspace { current_dir, current_branch } => {
                self.current_dir = current_dir.clone();
                self.current_branch = current_branch.clone();
                Command::Empty
            }
            Action::CrossTerm(event) => match event {
                ratatui::crossterm::event::Event::FocusGained => Command::Empty,
                ratatui::crossterm::event::Event::FocusLost => Command::Empty,
                ratatui::crossterm::event::Event::Key(key_event) => {
                    // Handle EXIT events first
                    use ratatui::crossterm::event::{KeyCode, KeyModifiers};
                    let ctrl = key_event.modifiers.contains(KeyModifiers::CONTROL);

                    if key_event.code == KeyCode::Char('d') && ctrl {
                        return Command::Exit;
                    }

                    self.router.update(action)
                }
                ratatui::crossterm::event::Event::Mouse(_) => self.router.update(action),
                ratatui::crossterm::event::Event::Paste(_) => Command::Empty,
                ratatui::crossterm::event::Event::Resize(_, _) => Command::Empty,
            },
            Action::Tagged(tagged) => {
                tagged.update("router", |action| self.router.update(action.to_owned()))
            }
            _ => Command::Empty,
        }
    }
}

impl Widget for App {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
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
            .position(|route| route == &self.router.current_route)
            .unwrap_or(0);

        Tabs::new(tab_titles)
            .style(Style::default().dark_gray())
            .highlight_style(Style::default().yellow().bold())
            .select(current_tab_index)
            .divider(" ")
            .render(tabs_area, buf);

        // Delegate content rendering to router with shared state
        self.router.render(content_area, buf);
    }
}
