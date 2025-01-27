#![allow(dead_code)]
use crossterm::style::Stylize;
use promptuity::event::*;
use promptuity::{
    InputCursor, Prompt, PromptBody, PromptInput, PromptState, RenderPayload, Validator,
};

/// A trait for formatting the [`AutocompleteInput`] prompt.
pub trait AutocompleteFormatter {
    /// Formats the suggestions list.
    fn suggestions(&self, suggestions: &[String], selected_index: usize) -> String {
        suggestions
            .iter()
            .enumerate()
            .map(|(i, suggestion)| {
                if i == selected_index {
                    format!(" {} {}", "→".cyan(), suggestion.as_str().cyan().bold())
                } else {
                    format!("   {}", suggestion)
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Formats the required error message.
    fn err_required(&self) -> String {
        "Required input".to_string()
    }
}

/// The default formatter for [`AutocompleteInput`].
#[derive(Default)]
pub struct DefaultAutocompleteFormatter;

impl DefaultAutocompleteFormatter {
    /// Creates a new [`DefaultAutocompleteFormatter`].
    pub fn new() -> Self {
        Self
    }
}

impl AutocompleteFormatter for DefaultAutocompleteFormatter {}

/// A trait for providing suggestions.
pub trait Suggester {
    /// Analyzes the input and returns suggestions if appropriate.
    /// This method handles both trigger detection and suggestion filtering.
    fn get_suggestions(&self, input: &str, cursor_position: usize) -> SuggestionContext;

    /// Formats the selected suggestion before it replaces the text in
    /// replace_range. Default implementation returns the suggestion as-is.
    fn format_suggestion(&self, suggestion: &str) -> String {
        suggestion.to_string()
    }
}

/// A simple suggester that filters a static list of suggestions when triggered
/// by a specific character.
pub struct StaticSuggester {
    pub suggestions: Vec<String>,
    pub trigger_chars: Vec<char>,
    pub submit_on_select: bool,
}

impl StaticSuggester {
    /// Creates a new [`StaticSuggester`] with the given suggestions.
    pub fn new(suggestions: Vec<String>) -> Self {
        let mut unique_suggestions: Vec<_> = suggestions.into_iter().collect();
        unique_suggestions.sort();
        Self {
            suggestions: unique_suggestions,
            trigger_chars: vec!['@'],
            submit_on_select: false,
        }
    }

    /// Sets the trigger characters that will activate suggestions
    pub fn with_triggers(mut self, triggers: Vec<char>) -> Self {
        self.trigger_chars = triggers;
        self
    }

    /// Sets whether selecting a suggestion should submit the input
    pub fn with_submit_on_select(mut self, submit: bool) -> Self {
        self.submit_on_select = submit;
        self
    }
}

impl Suggester for StaticSuggester {
    fn get_suggestions(&self, input: &str, cursor_position: usize) -> SuggestionContext {
        // Find the last trigger char before cursor position
        let input_before_cursor = &input[..cursor_position];
        if let Some((trigger_pos, _)) = input_before_cursor
            .char_indices()
            .rev()
            .find(|(_, c)| self.trigger_chars.contains(c))
        {
            let query = &input[trigger_pos + 1..cursor_position];
            let filtered = self
                .suggestions
                .iter()
                .filter(|s| s.to_lowercase().contains(&query.to_lowercase()))
                .cloned()
                .collect();

            SuggestionContext {
                suggestions: filtered,
                replace_range: Some((trigger_pos, cursor_position)),
                show_suggestions: !query.is_empty(),
                submit_on_select: self.submit_on_select,
            }
        } else {
            SuggestionContext {
                suggestions: Vec::new(),
                replace_range: None,
                show_suggestions: false,
                submit_on_select: false,
            }
        }
    }
}

/// A custom suggester that supports multiple trigger patterns and actions for
/// these triggers. eg. files with '@' and commands with '/'
pub struct MultiTriggerSuggester {
    files: StaticSuggester,
    commands: StaticSuggester,
}

impl MultiTriggerSuggester {
    pub fn new(files: Vec<String>, commands: Vec<String>) -> Self {
        Self {
            files: StaticSuggester::new(files)
                .with_triggers(vec!['@'])
                .with_submit_on_select(false), // Don't submit after selecting file
            commands: StaticSuggester::new(commands)
                .with_triggers(vec!['/'])
                .with_submit_on_select(true), // Submit immediately after selecting command
        }
    }
}

impl Suggester for MultiTriggerSuggester {
    fn get_suggestions(&self, input: &str, cursor_position: usize) -> SuggestionContext {
        // Find the last trigger char before cursor position
        let input_before_cursor = &input[..cursor_position];
        if let Some((trigger_pos, _)) = input_before_cursor
            .char_indices()
            .rev()
            .find(|(_, c)| self.commands.trigger_chars.contains(c))
        {
            let query = &input[trigger_pos + 1..cursor_position].to_lowercase();
            let filtered = self
                .commands
                .suggestions
                .iter()
                .filter(|s| s.to_lowercase().contains(query))
                .take(5)
                .cloned()
                .collect();

            SuggestionContext {
                suggestions: filtered,
                replace_range: Some((trigger_pos, cursor_position)),
                show_suggestions: !query.is_empty(),
                submit_on_select: self.commands.submit_on_select,
            }
        } else if let Some((trigger_pos, _)) = input_before_cursor
            .char_indices()
            .rev()
            .find(|(_, c)| self.files.trigger_chars.contains(c))
        {
            let query = &input[trigger_pos + 1..cursor_position].to_lowercase();
            let filtered = self
                .files
                .suggestions
                .iter()
                .filter(|s| {
                    let file = s.to_lowercase();
                    // we've file paths like '/users/abc/random/file.txt'
                    // we want to check on the basis of file name only
                    if let Some(file_name) = file.split('/').next_back() {
                        file_name.contains(query)
                    } else {
                        false
                    }
                })
                .take(5)
                .cloned()
                .collect();

            SuggestionContext {
                suggestions: filtered,
                replace_range: Some((trigger_pos, cursor_position)),
                show_suggestions: !query.is_empty(),
                submit_on_select: self.files.submit_on_select,
            }
        } else {
            SuggestionContext {
                suggestions: Vec::new(),
                replace_range: None,
                show_suggestions: false,
                submit_on_select: false,
            }
        }
    }
}

/// A prompt for text input with autocomplete suggestions.
pub struct AutocompleteInput<S: Suggester> {
    formatter: Box<dyn AutocompleteFormatter>,
    suggester: S,
    message: String,
    hint: Option<String>,
    placeholder: Option<String>,
    required: bool,
    validator: Option<Box<dyn Validator<String>>>,
    input: InputCursor,
    suggestion_context: Option<SuggestionContext>,
    selected_index: usize,
}

impl AutocompleteInput<StaticSuggester> {
    /// Creates a new [`AutocompleteInput`] prompt.
    pub fn new(message: impl std::fmt::Display) -> Self {
        Self {
            formatter: Box::new(DefaultAutocompleteFormatter::new()),
            suggester: StaticSuggester::new(Vec::new()),
            message: message.to_string(),
            hint: None,
            placeholder: None,
            required: true,
            validator: None,
            input: InputCursor::new(String::new(), 0),
            suggestion_context: None,
            selected_index: 0,
        }
    }
}

impl<S: Suggester> AutocompleteInput<S> {
    /// Creates a new [`AutocompleteInput`] prompt with a custom suggester.
    pub fn with_custom_suggester(message: impl std::fmt::Display, suggester: S) -> Self {
        Self {
            formatter: Box::new(DefaultAutocompleteFormatter::new()),
            suggester,
            message: message.to_string(),
            hint: None,
            placeholder: None,
            required: true,
            validator: None,
            input: InputCursor::new(String::new(), 0),
            suggestion_context: None,
            selected_index: 0,
        }
    }

    /// Sets the suggester for the prompt.
    pub fn with_suggester(mut self, suggester: S) -> Self {
        self.suggester = suggester;
        self
    }

    /// Sets the suggestions for the prompt.
    pub fn with_suggestions(self, suggestions: Vec<String>) -> AutocompleteInput<StaticSuggester> {
        AutocompleteInput {
            formatter: self.formatter,
            suggester: StaticSuggester::new(suggestions),
            message: self.message,
            hint: self.hint,
            placeholder: self.placeholder,
            required: self.required,
            validator: self.validator,
            input: self.input,
            suggestion_context: None,
            selected_index: 0,
        }
    }

    /// Sets the hint message for the prompt.
    pub fn with_hint(mut self, hint: impl std::fmt::Display) -> Self {
        self.hint = Some(hint.to_string());
        self
    }

    /// Sets the placeholder message for the prompt.
    pub fn with_placeholder(mut self, placeholder: impl std::fmt::Display) -> Self {
        self.placeholder = Some(placeholder.to_string());
        self
    }

    fn update_suggestions(&mut self) {
        let input = self.input.value();
        let cursor_pos = self.input.cursor();
        self.suggestion_context = Some(self.suggester.get_suggestions(&input, cursor_pos));
        self.selected_index = 0;
    }

    fn select_suggestion(&mut self) {
        if let Some(context) = &self.suggestion_context {
            if !context.suggestions.is_empty() && context.show_suggestions {
                if let Some((start, end)) = context.replace_range {
                    let input = self.input.value();
                    let suggestion = self
                        .suggester
                        .format_suggestion(&context.suggestions[self.selected_index]);
                    let new_value = format!("{}{}{}", &input[..start], suggestion, &input[end..]);
                    self.input = InputCursor::new(new_value, start + suggestion.len());
                }
            }
        }
        self.suggestion_context = None;
    }
}

impl<S: Suggester + 'static> AsMut<dyn Prompt<Output = String> + 'static> for AutocompleteInput<S> {
    fn as_mut(&mut self) -> &mut (dyn Prompt<Output = String> + 'static) {
        self
    }
}

impl<S: Suggester + 'static> AsMut<AutocompleteInput<S>> for AutocompleteInput<S> {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<S: Suggester + 'static> Prompt for AutocompleteInput<S> {
    type Output = String;

    fn submit(&mut self) -> Self::Output {
        self.input.value()
    }

    fn validate(&self) -> Result<(), String> {
        if let Some(validator) = &self.validator {
            validator.validate(&self.input.value())?;
        }
        Ok(())
    }

    fn handle(&mut self, code: KeyCode, modifiers: KeyModifiers) -> PromptState {
        match (code, modifiers) {
            (KeyCode::Esc, _) => {
                if self.suggestion_context.is_some() {
                    self.suggestion_context = None;
                    PromptState::Active
                } else {
                    PromptState::Cancel
                }
            }
            (KeyCode::Char('c'), KeyModifiers::CONTROL) => PromptState::Cancel,
            (KeyCode::Tab, _) | (KeyCode::Enter, _) => {
                if let Some(context) = &self.suggestion_context {
                    if !context.suggestions.is_empty() && context.show_suggestions {
                        let should_submit = context.submit_on_select;
                        self.select_suggestion();
                        if should_submit && self.validate().is_ok() {
                            return PromptState::Submit;
                        }
                        return PromptState::Active;
                    }
                }
                if code == KeyCode::Enter {
                    if self.input.is_empty() && self.required {
                        PromptState::Active
                    } else if self.validate().is_ok() {
                        PromptState::Submit
                    } else {
                        PromptState::Active
                    }
                } else {
                    PromptState::Active
                }
            }
            (KeyCode::Up, _) => {
                if let Some(context) = &mut self.suggestion_context {
                    if !context.suggestions.is_empty() {
                        self.selected_index = self.selected_index.saturating_sub(1);
                    }
                }
                PromptState::Active
            }
            (KeyCode::Down, _) => {
                if let Some(context) = &mut self.suggestion_context {
                    if !context.suggestions.is_empty() {
                        self.selected_index =
                            (self.selected_index + 1).min(context.suggestions.len() - 1);
                    }
                }
                PromptState::Active
            }
            (KeyCode::Left, _) | (KeyCode::Char('b'), KeyModifiers::CONTROL) => {
                self.input.move_left();
                PromptState::Active
            }
            (KeyCode::Right, _) | (KeyCode::Char('f'), KeyModifiers::CONTROL) => {
                self.input.move_right();
                PromptState::Active
            }
            (KeyCode::Home, _) | (KeyCode::Char('a'), KeyModifiers::CONTROL) => {
                self.input.move_home();
                PromptState::Active
            }
            (KeyCode::End, _) | (KeyCode::Char('e'), KeyModifiers::CONTROL) => {
                self.input.move_end();
                PromptState::Active
            }
            (KeyCode::Backspace, _) | (KeyCode::Char('h'), KeyModifiers::CONTROL) => {
                self.input.delete_left_char();
                self.update_suggestions();
                PromptState::Active
            }
            (KeyCode::Delete, _) | (KeyCode::Char('d'), KeyModifiers::CONTROL) => {
                self.input.delete_right_char();
                self.update_suggestions();
                PromptState::Active
            }
            (KeyCode::Char(c), KeyModifiers::NONE | KeyModifiers::SHIFT) => {
                self.input.insert(c);
                self.update_suggestions();
                PromptState::Active
            }
            _ => PromptState::Active,
        }
    }

    fn render(&mut self, _: &PromptState) -> Result<RenderPayload, String> {
        let mut payload = RenderPayload::new(
            self.message.clone(),
            self.hint.clone(),
            self.placeholder.clone(),
        );

        payload = payload.input(PromptInput::Cursor(self.input.clone()));

        if let Some(context) = &self.suggestion_context {
            if !context.suggestions.is_empty() && context.show_suggestions {
                payload = payload.body(PromptBody::Raw(
                    self.formatter
                        .suggestions(&context.suggestions, self.selected_index),
                ));
            }
        }

        Ok(payload)
    }
}

#[derive(Debug)]
pub struct SuggestionContext {
    pub suggestions: Vec<String>,
    pub show_suggestions: bool,
    pub replace_range: Option<(usize, usize)>,
    pub submit_on_select: bool,
}

impl SuggestionContext {
    pub fn found(&self) -> bool {
        !self.suggestions.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_autocomplete_input_basic() {
        let input = AutocompleteInput::new("Test")
            .with_suggestions(vec!["apple".to_string(), "banana".to_string()]);

        // Test initial state
        assert_eq!(input.input.value(), "");
        assert!(input.suggestion_context.is_none());
    }

    #[test]
    fn test_autocomplete_filtering() {
        let mut input = AutocompleteInput::new("Test").with_suggestions(vec![
            "apple".to_string(),
            "banana".to_string(),
            "apricot".to_string(),
        ]);

        // Simulate typing 'a'
        input.handle(KeyCode::Char('@'), KeyModifiers::NONE);
        input.handle(KeyCode::Char('a'), KeyModifiers::NONE);
        assert!(input.suggestion_context.is_some());

        // Simulate typing 'p'
        input.handle(KeyCode::Char('p'), KeyModifiers::NONE);
        assert!(input.suggestion_context.is_some());

        assert_eq!(
            input.suggestion_context.as_ref().unwrap().suggestions,
            vec!["apple".to_string(), "apricot".to_string()]
        );
    }

    #[test]
    fn test_suggestion_selection() {
        let mut input = AutocompleteInput::new("Test")
            .with_suggestions(vec!["apple".to_string(), "banana".to_string()]);

        // // Show suggestions
        input.handle(KeyCode::Char('@'), KeyModifiers::NONE);
        input.handle(KeyCode::Char('a'), KeyModifiers::NONE);
        input.handle(KeyCode::Char('p'), KeyModifiers::NONE);
        input.handle(KeyCode::Tab, KeyModifiers::NONE);
        assert_eq!(input.input.value(), "apple");
    }
}
