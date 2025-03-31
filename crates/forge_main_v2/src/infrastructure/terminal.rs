use std::io::Write;
use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Result;
use colored::Colorize;
use forge_api::{ChatResponse, Environment};
use forge_display::TitleFormat;

use super::console::CONSOLE;
use crate::application::{Completer, CompletionSuggestion, PromptContext, UserInterface};
use crate::domain::{CommandDefinition, CommandService};

/// Thread-safe adapter for storing completion state.
#[derive(Default, Clone)]
pub struct CompletionState {
    input: String,
    position: usize,
    suggestions: Vec<CompletionSuggestion>,
    current_index: usize,
}

pub struct TerminalUI {
    environment: Environment,
    verbose: bool,
    completer: Option<Arc<dyn Completer>>,
    completion_state: Arc<parking_lot::Mutex<CompletionState>>,
}

impl TerminalUI {
    pub fn new(environment: &Environment) -> Self {
        // Check verbose flag by inspecting the args
        // In a real implementation, this would come from CLI parsing
        let verbose = false; // Default value, in real implementation would come from CLI

        Self {
            environment: environment.clone(),
            verbose,
            completer: None,
            completion_state: Arc::new(parking_lot::Mutex::new(CompletionState::default())),
        }
    }

    pub fn with_completer(mut self, completer: Arc<dyn Completer>) -> Self {
        self.completer = Some(completer);
        self
    }

    pub fn with_command_service(mut self, command_service: Arc<dyn CommandService>) -> Self {
        // Create a default completer with the current directory and command service
        let cwd = PathBuf::from(&self.environment.cwd);
        let completer =
            Arc::new(InputCompleter::with_defaults(cwd, command_service)) as Arc<dyn Completer>;
        self.completer = Some(completer);
        self
    }

    pub fn display_banner(&self, command_names: Vec<String>) -> Result<()> {
        // Split the banner into lines and display each line dimmed
        let banner = include_str!("banner");
        println!("{} {}", banner.dimmed(), command_names.join(", ").bold());
        Ok(())
    }

    fn handle_tab_completion(&self, input: &mut String) -> bool {
        if let Some(ref completer) = self.completer {
            let mut state = self.completion_state.lock();

            // If we're continuing a completion sequence, cycle through suggestions
            if state.input == *input && !state.suggestions.is_empty() {
                state.current_index = (state.current_index + 1) % state.suggestions.len();
                let suggestion = &state.suggestions[state.current_index];

                // Replace the input text with the suggestion
                input.replace_range(
                    suggestion.span_start..suggestion.span_end,
                    &suggestion.value,
                );

                // Update state with new input
                state.input = input.clone();
                return true;
            }

            // Otherwise, get new suggestions
            state.input = input.clone();
            state.position = input.len();
            state.suggestions = completer.complete(input, input.len());
            state.current_index = 0;

            if !state.suggestions.is_empty() {
                let suggestion = &state.suggestions[0];

                // Replace the input text with the suggestion
                input.replace_range(
                    suggestion.span_start..suggestion.span_end,
                    &suggestion.value,
                );

                // Update state with new input
                state.input = input.clone();
                return true;
            }
        }
        false
    }
}

impl UserInterface for TerminalUI {
    fn display_message(&self, message: &ChatResponse) -> Result<()> {
        match message {
            ChatResponse::Text(text) => CONSOLE.write(text.dimmed().to_string())?,
            ChatResponse::ToolCallStart(_) => {
                CONSOLE.newline()?;
                CONSOLE.newline()?;
            }
            ChatResponse::ToolCallEnd(tool_result) => {
                // Skip tool results unless verbose
                if !self.verbose {
                    return Ok(());
                }

                let tool_name = tool_result.name.as_str();
                CONSOLE.writeln(format!("{}", tool_result.content.dimmed()))?;

                if tool_result.is_error {
                    CONSOLE.writeln(TitleFormat::failed(tool_name).format())?;
                } else {
                    CONSOLE.writeln(TitleFormat::success(tool_name).format())?;
                }
            }
            ChatResponse::Event(_) | ChatResponse::Usage(_) => {}
        }
        Ok(())
    }

    fn display_text(&self, text: &str) -> Result<()> {
        CONSOLE.write(text)?;
        Ok(())
    }

    fn display_error(&self, error: &str) -> Result<()> {
        CONSOLE.writeln(TitleFormat::failed(error).format())?;
        Ok(())
    }

    fn display_success(&self, message: &str, details: Option<&str>) -> Result<()> {
        let mut format = TitleFormat::success(message);
        if let Some(details) = details {
            format = format.sub_title(details);
        }
        CONSOLE.writeln(format.format())?;
        Ok(())
    }

    fn prompt_user(&self, prompt: &PromptContext) -> Result<String> {
        CONSOLE.newline()?;

        // Build prompt display string based on context
        let prompt_str = if let Some(title) = &prompt.title {
            format!("{} > ", title)
        } else if let Some(mode) = &prompt.mode {
            format!("{} > ", mode)
        } else {
            "> ".to_string()
        };

        print!("{}", prompt_str);
        std::io::stdout().flush().unwrap();

        // Simple line reading with tab completion
        let mut input = String::new();
        loop {
            if let crossterm::event::Event::Key(key_event) = crossterm::event::read()? {
                match key_event {
                    crossterm::event::KeyEvent {
                        code: crossterm::event::KeyCode::Enter, ..
                    } => {
                        println!(); // New line after input
                        break;
                    }
                    crossterm::event::KeyEvent { code: crossterm::event::KeyCode::Tab, .. } => {
                        // Handle tab completion
                        if self.handle_tab_completion(&mut input) {
                            // Clear line and redisplay prompt and updated input
                            print!("\r{}{}", prompt_str, input);
                            std::io::stdout().flush().unwrap();
                        }
                    }
                    crossterm::event::KeyEvent {
                        code: crossterm::event::KeyCode::Char(c), ..
                    } => {
                        input.push(c);
                        print!("{}", c);
                        std::io::stdout().flush().unwrap();
                    }
                    crossterm::event::KeyEvent {
                        code: crossterm::event::KeyCode::Backspace,
                        ..
                    } => {
                        if !input.is_empty() {
                            input.pop();
                            print!("\u{8} \u{8}"); // Backspace, space, backspace to clear the char
                            std::io::stdout().flush().unwrap();
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(input)
    }
}

/// Combined input completer implementation with CommandCompleter and
/// FileCompleter
pub struct InputCompleter {
    command_completer: Arc<CommandCompleter>,
    file_completer: Arc<FileCompleter>,
}

impl InputCompleter {
    pub fn new(
        command_completer: Arc<CommandCompleter>,
        file_completer: Arc<FileCompleter>,
    ) -> Self {
        Self { command_completer, file_completer }
    }

    /// Creates a new input completer with default implementations
    pub fn with_defaults(cwd: PathBuf, command_service: Arc<dyn CommandService>) -> Self {
        let command_completer = Arc::new(CommandCompleter::new(command_service));
        let file_completer = Arc::new(FileCompleter::new(cwd));

        Self::new(command_completer, file_completer)
    }
}

impl Completer for InputCompleter {
    fn complete(&self, input: &str, position: usize) -> Vec<CompletionSuggestion> {
        if input.starts_with('/') {
            // If the line starts with '/' it's probably a command
            let result = self.command_completer.complete_command(input, position);
            if !result.is_empty() {
                return result;
            }
        }

        // Otherwise, try to complete a file path
        self.file_completer.complete_path(input, position)
    }
}

/// Command completion implementation
pub struct CommandCompleter {
    command_service: Arc<dyn CommandService>,
}

impl CommandCompleter {
    pub fn new(command_service: Arc<dyn CommandService>) -> Self {
        Self { command_service }
    }

    pub fn complete_command(&self, input: &str, _position: usize) -> Vec<CompletionSuggestion> {
        self.command_service
            .list_commands()
            .into_iter()
            .filter(|cmd| cmd.name.starts_with(input))
            .map(|cmd| CommandDefinition {
                name: cmd.name.clone(),
                description: cmd.description.clone(),
                value: cmd.value.clone(),
            })
            .map(|cmd| CompletionSuggestion {
                value: cmd.name,
                description: Some(cmd.description),
                span_start: 0,
                span_end: input.len(),
                append_whitespace: false,
            })
            .collect()
    }
}

/// File path completion implementation
pub struct FileCompleter {
    cwd: PathBuf,
}

impl FileCompleter {
    pub fn new(cwd: PathBuf) -> Self {
        Self { cwd }
    }

    fn search_term(&self, input: &str, position: usize) -> Option<TermResult> {
        // Get all the indexes of the '@' chars
        input
            .chars()
            .enumerate()
            .filter(|(_, c)| *c == '@')
            .map(|(i, _)| i)
            .filter(|at| *at < position)
            .max_by(|a, b| a.cmp(b))
            .map(|at| TermResult {
                span_start: at + 1,
                span_end: position,
                term: input[at + 1..position].to_string(),
            })
            .filter(|s| !s.term.contains(' '))
    }

    pub fn complete_path(&self, input: &str, position: usize) -> Vec<CompletionSuggestion> {
        if let Some(query) = self.search_term(input, position) {
            // Get all files in directory
            let files = match std::fs::read_dir(&self.cwd) {
                Ok(entries) => entries
                    .filter_map(|entry| entry.ok())
                    .filter(|entry| {
                        if let Ok(file_type) = entry.file_type() {
                            !file_type.is_dir() // Only include files, not
                                                // directories
                        } else {
                            false
                        }
                    })
                    .filter_map(|entry| entry.file_name().to_str().map(|s| s.to_string()))
                    .collect::<Vec<_>>(),
                Err(_) => return vec![],
            };

            // Filter files based on query
            files
                .into_iter()
                .filter(|file_name| {
                    let file_name_lower = file_name.to_lowercase();
                    let query_lower = query.term.to_lowercase();
                    file_name_lower.contains(&query_lower)
                })
                .map(|file_name| CompletionSuggestion {
                    value: file_name,
                    description: None,
                    span_start: query.span_start,
                    span_end: query.span_end,
                    append_whitespace: true,
                })
                .collect()
        } else {
            vec![]
        }
    }
}

#[derive(Debug)]
pub struct TermResult {
    pub span_start: usize,
    pub span_end: usize,
    pub term: String,
}
