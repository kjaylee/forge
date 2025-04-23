use forge_api::{ConversationId, Mode, Model, ModelId, Usage};

use crate::prompt::ForgePrompt;

//TODO: UIState and ForgePrompt seem like the same thing and can be merged
/// State information for the UI
#[derive(Default, Clone)]
pub struct UIState {
    pub conversation_id: Option<ConversationId>,
    pub usage: Usage,
    pub is_first: bool,
    pub model: Option<ModelId>,
    pub cached_models: Option<Vec<Model>>,
}

impl UIState {
    pub fn new() -> Self {
        Self {
            conversation_id: Default::default(),
            usage: Default::default(),
            is_first: true,
            model: Default::default(),
            cached_models: Default::default(),
        }
    }
}

impl From<UIState> for ForgePrompt {
    fn from(state: UIState) -> Self {
        ForgePrompt {
            usage: Some(state.usage),
            model: state.model,
            mode: Mode::default(), // Default to Act mode
        }
    }
}
