use color_eyre::owo_colors::OwoColorize;
use edtui::{
    events::{KeyEvent, MouseEvent}, EditorEventHandler, EditorState, EditorStatusLine, EditorTheme, EditorView
};
use ratatui::{
    layout::{Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    text::Span,
    widgets::{Block, Borders, Padding, Widget},
};

#[derive(Default)]
pub struct App {
    editor: EditorEventHandler,
    editor_state: EditorState,
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

        let status = Span::styled(
            format!(" {} ", self.editor_state.mode.name().to_ascii_uppercase()),
            Style::default()
                .fg(Color::Black)
                .bg(Color::Yellow)
                .add_modifier(Modifier::BOLD),
        );

        let block = Block::new()
            .title(status)
            .borders(Borders::all())
            .padding(Padding::new(1, 1, 1, 1));

        EditorView::new(&mut self.editor_state)
            .theme(
                EditorTheme::default()
                    .base(Style::reset())
                    .hide_status_line(),
            )
            .wrap(true) // line wrapping
            .render(block.inner(user), buf);

        block.render(user, buf);
    }
}
