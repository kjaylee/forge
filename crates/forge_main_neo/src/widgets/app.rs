use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::text::Line;
use ratatui::widgets::{Tabs, Widget};

use crate::action::{Action, ChatAction, Route, RouterAction};
use crate::command::Command;
use crate::widgets::Router;

#[derive(Clone, Default, derive_setters::Setters)]
#[setters(strip_option, into)]
pub struct App {
    router: Router,
    pub current_branch: Option<String>,
    pub current_dir: Option<String>,
    pub current_route: Route,
}

impl App {
    #[must_use]
    pub fn update(&mut self, action: impl Into<Action>) -> Command {
        match action.into() {
            Action::Initialize => Command::ReadWorkspace,
            Action::Workspace { current_dir, current_branch } => {
                self.current_dir = current_dir;
                self.current_branch = current_branch;
                Command::Empty
            }
            Action::Router(router_action) => match router_action {
                RouterAction::NavigateToRoute(route) => {
                    self.router.navigate_to(route.clone());
                    self.current_route = route;
                    Command::Empty
                }
            },
            Action::Chat(chat_action) => match chat_action {
                ChatAction::MessageAdded(message) => {
                    self.router.add_user_chat_message(message);
                    Command::Empty
                }
            },
            Action::Help(_help_action) => {
                // Help actions can be handled here when implemented
                Command::Empty
            }
            Action::Settings(_settings_action) => {
                // Settings actions can be handled here when implemented
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
                        self.current_route = self.router.current_route.clone();
                        return Command::Empty;
                    }

                    if key_event.code == KeyCode::BackTab
                        || (key_event.code == KeyCode::Tab && shift)
                    {
                        self.router.navigate_previous();
                        self.current_route = self.router.current_route.clone();
                        return Command::Empty;
                    }

                    // Handle events based on current route
                    match self.current_route {
                        Route::Chat => self
                            .router
                            .chat
                            .handle_event(ratatui::crossterm::event::Event::Key(key_event)),
                        _ => self
                            .router
                            .update(ratatui::crossterm::event::Event::Key(key_event)),
                    }
                }
                ratatui::crossterm::event::Event::Mouse(mouse_event) => {
                    // Handle events based on current route
                    match self.current_route {
                        Route::Chat => self
                            .router
                            .chat
                            .handle_event(ratatui::crossterm::event::Event::Mouse(mouse_event)),
                        _ => self
                            .router
                            .update(ratatui::crossterm::event::Event::Mouse(mouse_event)),
                    }
                }
                ratatui::crossterm::event::Event::Paste(_) => Command::Empty,
                ratatui::crossterm::event::Event::Resize(_, _) => Command::Empty,
            },
            Action::ChatResponse { message } => {
                self.router.add_chat_message(message);
                Command::Empty
            }
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
            .position(|route| route == &self.current_route)
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

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_app_setters() {
        let mut fixture = App::default();

        // Test setters work with the derive_setters attributes
        fixture = fixture.current_branch("main".to_string());
        fixture = fixture.current_dir("/path/to/dir".to_string());
        fixture = fixture.current_route(Route::Chat);

        assert_eq!(fixture.current_branch, Some("main".to_string()));
        assert_eq!(fixture.current_dir, Some("/path/to/dir".to_string()));
        assert_eq!(fixture.current_route, Route::Chat);
    }
}
