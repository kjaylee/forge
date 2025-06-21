use edtui::events::{KeyEvent, MouseEvent};
use edtui::{EditorEventHandler, EditorState, EditorTheme, EditorView};
use ratatui::layout::{Alignment, Constraint, Direction, Layout};
use ratatui::style::{Style, Stylize};
use ratatui::symbols::{border, line};
use ratatui::widgets::{Block, Borders, Padding, Paragraph, Widget};

use crate::widgets::status::StatusBar;

#[derive(Default)]
pub struct App {
    editor: EditorEventHandler,
    editor_state: EditorState,
    state: State,
}

#[derive(Default)]
pub struct State {
    messages: Vec<String>,
}

impl App {
    pub fn on_key_event<T>(&mut self, key_event: T)
    where
        T: Into<KeyEvent>,
    {
        self.editor.on_key_event(key_event, &mut self.editor_state);
    }

    pub fn on_mouse_event<T>(&mut self, key_event: T)
    where
        T: Into<MouseEvent>,
    {
        self.editor
            .on_mouse_event(key_event, &mut self.editor_state);
    }
}

impl Widget for &mut App {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        let main_layout = Layout::new(
            Direction::Vertical,
            [Constraint::Fill(0), Constraint::Max(6)],
        );
        let [ass, user] = main_layout.areas(area);

        let content_block = Block::bordered()
            .title(" Welcome to Forge ")
            .padding(Padding::new(0, 0, 4, 0))
            .title_alignment(Alignment::Center)
            .border_set(border::Set {
                bottom_right: line::VERTICAL_LEFT,
                bottom_left: line::VERTICAL_RIGHT,
                ..border::PLAIN
            })
            .border_style(Style::default().dark_gray())
            .title_style(Style::default().dark_gray());

        let content = Paragraph::new(vec![
            "Use <CTRL+D> to exit".into(),
            "Use <CTRL+T> to toggle between PLAN & ACT mode".into(),
        ])
        .style(Style::default().dark_gray())
        .centered()
        .block(content_block);

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
            .title_bottom(StatusBar::new("FORGE", self.editor_state.mode.name()));

        EditorView::new(&mut self.editor_state)
            .theme(
                EditorTheme::default()
                    .base(Style::reset())
                    .hide_status_line(),
            )
            .wrap(true) // line wrapping
            .render(user_block.inner(user), buf);

        content.render(ass, buf);
        user_block.render(user, buf);
    }
}
