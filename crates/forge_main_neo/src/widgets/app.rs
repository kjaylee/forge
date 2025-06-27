use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Tabs, Widget};

use crate::model::{Action, Command, State};
use crate::widgets::{Route, Router};

#[derive(Default)]
pub struct App {
    router: Router,
    state: State,
}

impl App {
    #[must_use]
    pub fn update(&mut self, action: impl Into<Action>) -> Command {
        match action.into() {
            Action::Initialize => Command::ReadWorkspace,
            Action::Workspace { current_dir, current_branch } => {
                self.state.current_dir = current_dir;
                self.state.current_branch = current_branch;
                Command::Empty
            }
            Action::NavigateToRoute(route) => {
                self.router.navigate_to(route.clone());
                self.state.current_route = route;
                Command::Empty
            }
            Action::NavigateNext => {
                self.router.navigate_next();
                self.state.current_route = self.router.current_route.clone();
                Command::Empty
            }
            Action::NavigatePrevious => {
                self.router.navigate_previous();
                self.state.current_route = self.router.current_route.clone();
                Command::Empty
            }
            Action::CrossTerm(event) => match event {
                ratatui::crossterm::event::Event::FocusGained => Command::Empty,
                ratatui::crossterm::event::Event::FocusLost => Command::Empty,
                ratatui::crossterm::event::Event::Key(key_event) => {
                    use ratatui::crossterm::event::{KeyCode, KeyModifiers};
                    let ctrl = key_event.modifiers.contains(KeyModifiers::CONTROL);
                    let shift = key_event.modifiers.contains(KeyModifiers::SHIFT);

                    if key_event.code == KeyCode::Char('d') && ctrl {
                        return Command::Exit;
                    }

                    // Navigation shortcuts
                    if key_event.code == KeyCode::Tab && !shift {
                        self.router.navigate_next();
                        self.state.current_route = self.router.current_route.clone();
                        return Command::Empty;
                    }

                    if key_event.code == KeyCode::BackTab
                        || (key_event.code == KeyCode::Tab && shift)
                    {
                        self.router.navigate_previous();
                        self.state.current_route = self.router.current_route.clone();
                        return Command::Empty;
                    }

                    // Delegate other key events to router
                    self.router
                        .handle_event(ratatui::crossterm::event::Event::Key(key_event))
                }
                ratatui::crossterm::event::Event::Mouse(mouse_event) => {
                    // Delegate mouse events to router
                    self.router
                        .handle_event(ratatui::crossterm::event::Event::Mouse(mouse_event))
                }
                ratatui::crossterm::event::Event::Paste(_) => Command::Empty,
                ratatui::crossterm::event::Event::Resize(_, _) => Command::Empty,
            },
            Action::ChatResponse { message } => {
                self.state.messages.push(message);
                Command::Empty
            }
        }
    }
}

impl Widget for &App {
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
            .position(|route| route == &self.state.current_route)
            .unwrap_or(0);

        Tabs::new(tab_titles)
            .style(Style::default().dark_gray())
            .highlight_style(Style::default().yellow().bold())
            .select(current_tab_index)
            .divider(" ")
            .render(tabs_area, buf);

        // Delegate content rendering to router
        self.router.render(content_area, buf);
    }
}
