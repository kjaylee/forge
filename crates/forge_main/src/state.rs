use forge_api::{ConversationId, Usage};

use crate::input::PromptInput;

#[derive(Clone)]
pub struct Mode(String);

impl Mode {
    pub fn new(value: impl ToString) -> Self {
        Self(value.to_string().to_uppercase())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Default for Mode {
    fn default() -> Self {
        Self::new("ACT")
    }
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Built-in mode constants for backwards compatibility
impl Mode {
    pub fn act() -> Self {
        Self::new("ACT")
    }

    pub fn plan() -> Self {
        Self::new("PLAN")
    }

    pub fn help() -> Self {
        Self::new("HELP")
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
    pub mode: Mode,
    pub is_first: bool,
}

impl Default for UIState {
    fn default() -> Self {
        Self {
            current_title: Default::default(),
            conversation_id: Default::default(),
            usage: Default::default(),
            mode: Default::default(),
            is_first: true,
        }
    }
}

impl From<&UIState> for PromptInput {
    fn from(state: &UIState) -> Self {
        PromptInput::Update {
            title: state.current_title.clone(),
            usage: Some(state.usage.clone()),
            mode: state.mode.clone(),
        }
    }
}
