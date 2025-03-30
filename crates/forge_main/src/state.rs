use forge_api::{ConversationId, Usage};

use crate::input::PromptInput;

#[derive(Clone, Debug, PartialEq)]
pub struct Mode(String);

impl Mode {
    pub fn new(value: impl ToString) -> Self {
        Self(value.to_string().to_uppercase())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// PartialEq implementations for string comparisons
impl PartialEq<str> for Mode {
    fn eq(&self, other: &str) -> bool {
        self.0.eq_ignore_ascii_case(other)
    }
}

impl PartialEq<&str> for Mode {
    fn eq(&self, other: &&str) -> bool {
        self.0.eq_ignore_ascii_case(other)
    }
}

impl PartialEq<String> for Mode {
    fn eq(&self, other: &String) -> bool {
        self.0.eq_ignore_ascii_case(other)
    }
}

/// State information for the UI
pub struct UIState {
    pub current_title: Option<String>,
    pub conversation_id: Option<ConversationId>,
    pub usage: Usage,
    pub mode: Option<Mode>,
    pub is_first: bool,
}

impl UIState {
    /// Get the current mode or return an error if no mode is set
    pub fn get_mode(&self) -> anyhow::Result<&Mode> {
        self.mode.as_ref().ok_or_else(|| {
            anyhow::anyhow!(
                "No mode defined. At least one mode must be configured in the workflow."
            )
        })
    }
}

impl Default for UIState {
    fn default() -> Self {
        Self {
            current_title: Default::default(),
            conversation_id: Default::default(),
            usage: Default::default(),
            mode: None,
            is_first: true,
        }
    }
}

impl From<&UIState> for PromptInput {
    fn from(state: &UIState) -> Self {
        // Try to get the mode, but fallback to None if it's not available
        // This is safe because PromptInput can handle Option<Mode>
        let mode = state.mode.clone();
        PromptInput::Update {
            title: state.current_title.clone(),
            usage: Some(state.usage.clone()),
            mode,
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_get_mode_with_mode() {
        // Create UIState with a mode
        let state = UIState {
            current_title: None,
            conversation_id: None,
            usage: Usage::default(),
            mode: Some(Mode::new("ACT")),
            is_first: true,
        };

        // Test get_mode returns the mode
        let mode = state.get_mode().expect("Mode should be present");
        assert_eq!(mode.as_str(), "ACT");
    }

    #[test]
    fn test_get_mode_without_mode() {
        // Create UIState without a mode
        let state = UIState {
            current_title: None,
            conversation_id: None,
            usage: Usage::default(),
            mode: None,
            is_first: true,
        };

        // Test get_mode returns an error
        let result = state.get_mode();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("No mode defined"));
    }
}
