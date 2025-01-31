use std::borrow::Cow;

use forge_domain::Command;
use nu_ansi_term::{Color, Style};
use reedline::{
    default_emacs_keybindings, ColumnarMenu, Completer, DefaultHinter, EditCommand, Emacs,
    FileBackedHistory, KeyCode, KeyModifiers, MenuBuilder, Prompt, PromptHistorySearchStatus,
    Reedline, ReedlineEvent, ReedlineMenu, Signal, Span, Suggestion,
};

// cap the title by `MAX_LEN` chars else show ellipsis at the end.
const MAX_LEN: usize = 30;

pub struct ReedLineEngine {
    editor: Reedline,
    prompt: Box<dyn Prompt>,
}

#[derive(Clone)]
struct CommandCompleter {
    commands: Vec<String>,
}

#[derive(Clone, Default)]
pub struct CustomPrompt {
    title: Option<String>,
}

impl CustomPrompt {
    pub fn with_title<T: Into<String>>(mut self, title: T) -> Self {
        self.title = Some(title.into());
        self
    }
}

impl Prompt for CustomPrompt {
    fn render_prompt_left(&self) -> Cow<str> {
        if let Some(title) = self.title.as_ref() {
            // TODO: cap the title by 15 chars else show ellipsis at the end.
            let truncated = if title.chars().count() > MAX_LEN {
                format!("{}...", title.chars().take(MAX_LEN).collect::<String>())
            } else {
                title.to_string()
            };

            Cow::Owned(format!(
                "{} {} {}{}{}",
                Style::new()
                    .reset_before_style()
                    .bold()
                    .fg(Color::LightGreen)
                    .paint("➜"),
                Style::new().fg(Color::Cyan).bold().paint("FORGE"),
                Style::new().fg(Color::Blue).bold().paint("("),
                Style::new()
                    .reset_before_style()
                    .bold()
                    .fg(Color::Red)
                    .paint(truncated),
                Style::new().fg(Color::Blue).bold().paint(")")
            ))
        } else {
            Cow::Owned(format!(
                "{} {}",
                Style::new()
                    .reset_before_style()
                    .bold()
                    .fg(Color::LightGreen)
                    .paint("➜"),
                Style::new().fg(Color::Cyan).bold().paint("FORGE"),
            ))
        }
    }

    fn render_prompt_right(&self) -> Cow<str> {
        Cow::Borrowed("")
    }

    fn render_prompt_indicator(&self, _prompt_mode: reedline::PromptEditMode) -> Cow<str> {
        Cow::Owned(format!(
            " {} ",
            Style::new().fg(Color::LightYellow).bold().paint("⚡")
        ))
    }

    fn render_prompt_multiline_indicator(&self) -> Cow<str> {
        Cow::Borrowed("::: ")
    }

    fn render_prompt_history_search_indicator(
        &self,
        history_search: reedline::PromptHistorySearch,
    ) -> Cow<str> {
        let prefix = match history_search.status {
            PromptHistorySearchStatus::Passing => "",
            PromptHistorySearchStatus::Failing => "failing ",
        };
        Cow::Owned(format!(
            "({}reverse-search: {}) ",
            prefix, history_search.term
        ))
    }
}

impl Default for CommandCompleter {
    fn default() -> Self {
        Self { commands: Command::available_commands() }
    }
}

impl Completer for CommandCompleter {
    fn complete(&mut self, line: &str, _pos: usize) -> Vec<Suggestion> {
        self.commands
            .iter()
            .filter(|cmd| cmd.starts_with(line))
            .map(|cmd| Suggestion {
                value: cmd.to_string(),
                description: None,
                style: None,
                extra: None,
                span: Span::new(0, line.len()),
                append_whitespace: true,
            })
            .collect()
    }
}

impl ReedLineEngine {
    fn intialize_bindings() -> reedline::Keybindings {
        let mut keybindings = default_emacs_keybindings();
        // on TAB press shows the completion menu, and if we've exact match it will
        // insert it
        keybindings.add_binding(
            KeyModifiers::NONE,
            KeyCode::Tab,
            ReedlineEvent::UntilFound(vec![
                ReedlineEvent::Menu("completion_menu".to_string()),
                ReedlineEvent::MenuNext,
                ReedlineEvent::Edit(vec![EditCommand::Complete]),
            ]),
        );

        // on CTRL + k press clears the screen
        keybindings.add_binding(
            KeyModifiers::CONTROL,
            KeyCode::Char('k'),
            ReedlineEvent::ClearScreen,
        );

        // on ALT + Enter press inserts a newline
        keybindings.add_binding(
            KeyModifiers::ALT,
            KeyCode::Enter,
            ReedlineEvent::Edit(vec![EditCommand::InsertNewline]),
        );

        keybindings
    }

    pub fn start() -> Self {
        let history = Box::new(FileBackedHistory::default());
        let completion_menu = Box::new(
            ColumnarMenu::default()
                .with_name("completion_menu")
                .with_marker("➜ ")
                .with_text_style(Style::new().dimmed().italic().fg(Color::White))
                .with_selected_text_style(
                    Style::new()
                        .reset_before_style()
                        .bold()
                        .fg(Color::White)
                        .bold(),
                )
                .with_column_width(Some(40)),
        );

        let edit_mode = Box::new(Emacs::new(Self::intialize_bindings()));
        let completer = Box::new(CommandCompleter::default());
        let editor = Reedline::create()
            .with_history(history)
            .with_completer(completer)
            .with_hinter(Box::new(
                DefaultHinter::default().with_style(Style::new().italic().fg(Color::DarkGray)),
            ))
            .with_menu(ReedlineMenu::EngineCompleter(completion_menu))
            .with_edit_mode(edit_mode)
            .with_quick_completions(true)
            .with_partial_completions(true)
            .with_ansi_colors(true);
        let prompt = CustomPrompt::default();
        Self { editor, prompt: Box::new(prompt) }
    }

    #[allow(dead_code)]
    pub fn with_prompt(mut self, prompt: Box<dyn Prompt>) -> Self {
        self.prompt = prompt;
        self
    }

    pub fn prompt(&mut self) -> anyhow::Result<ReadResult> {
        let signal = self.editor.read_line(&*self.prompt);
        signal.map(Into::into).map_err(|e| anyhow::anyhow!(e))
    }
}

pub enum ReadResult {
    Success(String),
    Continue,
    Exit,
}

impl From<Signal> for ReadResult {
    fn from(signal: Signal) -> Self {
        match signal {
            Signal::Success(buffer) => ReadResult::Success(buffer),
            Signal::CtrlC => ReadResult::Continue,
            Signal::CtrlD => ReadResult::Exit,
        }
    }
}
