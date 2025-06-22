use edtui::{EditorEventHandler, EditorMode, EditorTheme, EditorView};
use ratatui::crossterm::event::{KeyCode, KeyModifiers};
use ratatui::layout::{Alignment, Constraint, Direction, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::text::Line;
use ratatui::widgets::{Block, Borders, Padding, Paragraph, StatefulWidget, Widget};

use crate::model::{Action, Command, State};
use crate::widgets::status::StatusBar;

#[derive(Default)]
pub struct App {
    editor: EditorEventHandler,
}

impl App {
    #[must_use]
    pub fn update(&mut self, action: impl Into<Action>, state: &mut State) -> Command {
        match action.into() {
            Action::Initialize => Command::Empty,
            Action::CrossTerm(event) => match event {
                ratatui::crossterm::event::Event::FocusGained => Command::Empty,
                ratatui::crossterm::event::Event::FocusLost => Command::Empty,
                ratatui::crossterm::event::Event::Key(event) => {
                    let ctrl = event.modifiers.contains(KeyModifiers::CONTROL);
                    if event.code == KeyCode::Char('d') && ctrl {
                        return Command::Exit;
                    }

                    // Submit
                    if event.code == KeyCode::Enter && state.editor.mode == EditorMode::Normal {
                        let message = state.take_lines().join("\n");
                        state.messages.push(message.clone());
                        return Command::Chat(message);
                    }

                    self.editor.on_key_event(event, &mut state.editor);
                    Command::Empty
                }
                ratatui::crossterm::event::Event::Mouse(event) => {
                    self.editor.on_mouse_event(event, &mut state.editor);
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
        let main_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(6)],
        );
        let [ass, user] = main_layout.areas(area);

        let content_block = Block::bordered()
            .title(" Welcome to Forge ")
            .title_alignment(Alignment::Center)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        let content_paragraph = if state.messages.is_empty() {
            let content_block_with_padding = content_block.padding(Padding::new(0, 0, 4, 0));

            Paragraph::new(vec![
                "Use <CTRL+D> to exit".into(),
                "Use <CTRL+T> to toggle between PLAN & ACT mode".into(),
            ])
            .style(Style::default().dark_gray())
            .centered()
            .block(content_block_with_padding)
        } else {
            // Need to create a paragraph from each line.
            Paragraph::new(state.messages.iter().map(Line::raw).collect::<Vec<_>>())
                .block(content_block)
        };

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
            .title_bottom(StatusBar::new("FORGE", state.editor.mode.name()));

        EditorView::new(&mut state.editor)
            .theme(
                EditorTheme::default()
                    .base(Style::reset())
                    .hide_status_line(),
            )
            .wrap(true) // line wrapping
            .render(user_block.inner(user), buf);

        content_paragraph.render(ass, buf);
        user_block.render(user, buf);
    }
}
