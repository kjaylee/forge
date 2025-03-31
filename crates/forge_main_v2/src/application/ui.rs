use anyhow::Result;
use forge_api::{ChatResponse, Usage};

use crate::domain::ForgeMode;

/// Result of a completion operation.
#[derive(Debug, Clone)]
pub struct CompletionSuggestion {
    /// The value to insert when selected.
    pub value: String,
    /// Description of the suggestion.
    pub description: Option<String>,
    /// The span in the input string where the suggestion applies.
    pub span_start: usize,
    /// The end of the span in the input string.
    pub span_end: usize,
    /// Whether to append whitespace after inserting the suggestion.
    pub append_whitespace: bool,
}

/// Interface for completing user input.
pub trait Completer: Send + Sync {
    /// Complete the given input at the given position.
    fn complete(&self, input: &str, position: usize) -> Vec<CompletionSuggestion>;
}

/// Interface for user interface implementations
pub trait UserInterface: Send + Sync {
    fn display_message(&self, message: &ChatResponse) -> Result<()>;
    fn display_text(&self, text: &str) -> Result<()>;
    fn display_error(&self, error: &str) -> Result<()>;
    fn display_success(&self, message: &str, details: Option<&str>) -> Result<()>;
    fn prompt_user(&self, prompt: &PromptContext) -> Result<String>;
}

/// Context for prompting the user
pub struct PromptContext {
    pub title: Option<String>,
    pub usage: Option<Usage>,
    pub mode: Option<ForgeMode>,
}

impl Default for PromptContext {
    fn default() -> Self {
        Self::new()
    }
}

impl PromptContext {
    pub fn new() -> Self {
        Self { title: None, usage: None, mode: None }
    }

    pub fn with_title(mut self, title: impl ToString) -> Self {
        self.title = Some(title.to_string());
        self
    }

    pub fn with_usage(mut self, usage: Usage) -> Self {
        self.usage = Some(usage);
        self
    }

    pub fn with_mode(mut self, mode: ForgeMode) -> Self {
        self.mode = Some(mode);
        self
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_prompt_context_builder() {
        let fixture = PromptContext::new()
            .with_title("Test Title")
            .with_usage(Usage::default())
            .with_mode(ForgeMode::new("ACT"));

        assert_eq!(fixture.title, Some("Test Title".to_string()));
        assert!(fixture.usage.is_some());
        assert_eq!(fixture.mode.as_ref().unwrap(), "ACT");
    }
}
