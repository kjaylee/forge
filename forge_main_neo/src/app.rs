// Remove unused import and use ratatui's crossterm consistently
use forge_api::ModelId;
use ratatui::crossterm::event::{Event, KeyCode, KeyEvent, KeyModifiers};
use ratatui::crossterm::style::Color;
use ratatui::layout::Alignment;
use ratatui::style::{Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, BorderType, Widget};
use ratatui::{DefaultTerminal, Frame};
use tui_textarea::TextArea;

#[derive(Debug)]
pub struct App {
    state: State,
    text_area: TextArea<'static>,
}

#[derive(Debug, Default)]
pub struct State {
    model_id: Option<ModelId>,
    exit: bool,
    suspend: bool,
}

impl State {
    fn handle_key_event(&mut self, key_event: KeyEvent) {
        if let KeyEvent {
            code: _code @ KeyCode::Char(char),
            modifiers: KeyModifiers::CONTROL,
            ..
        } = key_event
        {
            if char == 'd' {
                self.exit = true;
            }

            if char == 'c' {
                self.suspend = true;
            }
        }
    }
}

impl App {
    pub fn new() -> Self {
        let mut text_area = TextArea::default();
        text_area.set_style(Style::default());
        Self { state: State::default(), text_area }
    }
    pub fn run(&mut self, terminal: &mut DefaultTerminal) -> anyhow::Result<()> {
        while !self.state.exit {
            terminal.draw(|frame| self.draw(frame))?;
            if let Event::Key(key) = ratatui::crossterm::event::read()? {
                self.text_area.input(key);
                self.state.handle_key_event(key)
            }
        }
        Ok(())
    }

    fn draw(&self, frame: &mut Frame) {
        frame.render_widget(self, frame.area());
    }
}

struct KBShortcutsLine;

impl<'a> From<KBShortcutsLine> for Line<'a> {
    fn from(_val: KBShortcutsLine) -> Self {
        Line::from(vec![
            Span::from(" EXIT "),
            Span::from("<CTRL+D>").bg(Color::Grey),
            Span::from(" STOP "),
            Span::from("<CTRL+C>").bg(Color::Grey),
            Span::from(" RUN "),
            Span::from("<CTRL+R>").bg(Color::Grey),
            Span::from(" MODE "),
            Span::from("<CTRL+M>").bg(Color::Grey),
            Span::from(" "),
        ])
        .centered()
        .bold()
    }
}

impl Widget for &App {
    fn render(self, area: ratatui::prelude::Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        let block = Block::new()
            .title_style(Style::default().dark_gray())
            .title_bottom(KBShortcutsLine);

        let inner_area = block.inner(area);
        self.text_area.render(inner_area, buf);
        block.render(area, buf);
    }
}
