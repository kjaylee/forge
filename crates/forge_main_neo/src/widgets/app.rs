use edtui::{EditorEventHandler, EditorMode, EditorTheme, EditorView};
use ratatui::crossterm::event::{KeyCode, KeyModifiers};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::text::Line;
use ratatui::widgets::{Block, Borders, Padding, StatefulWidget, Tabs, Widget};

use crate::model::{Action, Command, State};
use crate::widgets::message_list::MessageList;
use crate::widgets::status_bar::StatusBar;
use crate::widgets::{Route, Router};

#[derive(Default)]
pub struct App {
    editor: EditorEventHandler,
    router: Router,
}

impl App {
    #[must_use]
    pub fn update(&mut self, action: impl Into<Action>, state: &mut State) -> Command {
        match action.into() {
            Action::Initialize => Command::ReadWorkspace,
            Action::Workspace { current_dir, current_branch } => {
                state.current_dir = current_dir;
                state.current_branch = current_branch;
                Command::Empty
            }
            Action::NavigateToRoute(route) => {
                self.router.navigate_to(route.clone());
                state.current_route = route;
                Command::Empty
            }
            Action::NavigateNext => {
                self.router.navigate_next();
                state.current_route = self.router.current_route().clone();
                Command::Empty
            }
            Action::NavigatePrevious => {
                self.router.navigate_previous();
                state.current_route = self.router.current_route().clone();
                Command::Empty
            }
            Action::CrossTerm(event) => match event {
                ratatui::crossterm::event::Event::FocusGained => Command::Empty,
                ratatui::crossterm::event::Event::FocusLost => Command::Empty,
                ratatui::crossterm::event::Event::Key(event) => {
                    let ctrl = event.modifiers.contains(KeyModifiers::CONTROL);
                    let shift = event.modifiers.contains(KeyModifiers::SHIFT);

                    if event.code == KeyCode::Char('d') && ctrl {
                        return Command::Exit;
                    }

                    // Navigation shortcuts
                    if event.code == KeyCode::Tab && !shift {
                        self.router.navigate_next();
                        state.current_route = self.router.current_route().clone();
                        return Command::Empty;
                    }

                    if event.code == KeyCode::BackTab || (event.code == KeyCode::Tab && shift) {
                        self.router.navigate_previous();
                        state.current_route = self.router.current_route().clone();
                        return Command::Empty;
                    }

                    // Submit - only in Chat route
                    if event.code == KeyCode::Enter
                        && state.editor.mode == EditorMode::Normal
                        && state.current_route == Route::Chat
                    {
                        let message = state.take_lines().join("\n");
                        state.messages.push(message.clone());
                        return Command::Chat(message);
                    }

                    // Only handle editor events in Chat route
                    if state.current_route == Route::Chat {
                        self.editor.on_key_event(event, &mut state.editor);
                    }
                    Command::Empty
                }
                ratatui::crossterm::event::Event::Mouse(event) => {
                    // Only handle mouse events in Chat route
                    if state.current_route == Route::Chat {
                        self.editor.on_mouse_event(event, &mut state.editor);
                    }
                    Command::Empty
                }
                ratatui::crossterm::event::Event::Paste(_) => Command::Empty,
                ratatui::crossterm::event::Event::Resize(_, _) => Command::Empty,
            },
            Action::ChatResponse { message } => {
                state.messages.push(message);
                Command::Empty
            }
        }
    }
}

impl StatefulWidget for &App {
    type State = State;
    fn render(
        self,
        area: ratatui::prelude::Rect,
        buf: &mut ratatui::prelude::Buffer,
        state: &mut Self::State,
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

        match state.current_route {
            Route::Chat => {
                // Render the chat interface with editor
                let chat_layout = Layout::new(
                    Direction::Vertical,
                    [Constraint::Fill(0), Constraint::Max(3)],
                );
                let [messages_area, user_area] = chat_layout.areas(content_area);

                let content_block = Block::bordered()
                    // .border_set(border::PROPORTIONAL_TALL)
                    .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT | Borders::TOP)
                    .border_set(border::Set {
                        bottom_right: line::VERTICAL_LEFT,
                        bottom_left: line::VERTICAL_RIGHT,
                        ..border::PLAIN
                    })
                    .border_style(Style::default().dark_gray())
                    .title_style(Style::default().dark_gray());

                MessageList::default()
                    .messages(state.messages.clone())
                    .render(content_block.inner(messages_area), buf);

                let user_block = Block::bordered()
                    .padding(Padding::new(0, 0, 0, 1))
                    .border_set(border::Set {
                        top_left: line::VERTICAL_RIGHT,
                        top_right: line::VERTICAL_LEFT,
                        ..border::PLAIN
                    })
                    .borders(Borders::BOTTOM | Borders::LEFT | Borders::RIGHT)
                    .title_style(Style::default().dark_gray())
                    .border_style(Style::default().dark_gray())
                    .title_bottom(StatusBar::new(
                        "FORGE",
                        state.editor.mode.name(),
                        state.current_branch.clone(),
                        state.current_dir.clone(),
                    ));

                EditorView::new(&mut state.editor)
                    .theme(
                        EditorTheme::default()
                            .base(Style::reset())
                            .cursor_style(Style::default().fg(Color::Black).bg(Color::White))
                            .hide_status_line(),
                    )
                    .wrap(true)
                    .render(user_block.inner(user_area), buf);

                content_block.render(messages_area, buf);
                user_block.render(user_area, buf);
            }
            _ => {
                // For other routes, render without status bar
                self.router.render(content_area, buf, state);
            }
        }
    }
}
