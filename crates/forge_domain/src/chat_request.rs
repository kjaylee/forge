use std::collections::HashMap;

use derive_setters::Setters;

use crate::{ConversationId, ModelId};

#[derive(Debug, Default, Clone, serde::Deserialize, serde::Serialize)]
pub struct TemplateVars(HashMap<String, String>);

impl From<HashMap<String, String>> for TemplateVars {
    fn from(map: HashMap<String, String>) -> Self {
        Self(map)
    }
}

impl TemplateVars {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn set(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.0.insert(key.into(), value.into());
        self
    }
}

#[derive(Debug, serde::Deserialize, Clone, Setters)]
#[setters(into)]
pub struct ChatRequest {
    pub content: String,
    pub model: ModelId,
    pub conversation_id: Option<ConversationId>,
    pub template_vars: TemplateVars,
}

impl ChatRequest {
    pub fn new(content: impl ToString) -> Self {
        Self {
            content: content.to_string(),
            model: ModelId::default(),
            conversation_id: None,
            template_vars: TemplateVars::new(),
        }
    }
}
