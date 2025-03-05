use forge_api::{ConversationId, Usage};

use crate::input::PromptInput;

/// State information for the UI
#[derive(Default)]
pub(crate) struct UIState {
    pub(crate) current_title: Option<String>,
    pub(crate) conversation_id: Option<ConversationId>,
    pub(crate) usage: Usage,
}

impl From<&UIState> for PromptInput {
    fn from(state: &UIState) -> Self {
        PromptInput::Update {
            title: state.current_title.clone(),
            usage: Some(state.usage.clone()),
        }
    }
}
