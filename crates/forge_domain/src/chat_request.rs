use std::path::PathBuf;

use derive_setters::Setters;

use crate::Workflow;

#[derive(Debug, serde::Deserialize, Clone, Setters)]
#[setters(into, strip_option)]
pub struct ChatRequest {
    pub content: String,
    // FIXME: drop custom-instructions
    pub custom_instructions: Option<PathBuf>,
    pub workflow: Workflow,
}

impl ChatRequest {
    pub fn new(content: impl ToString, workflow: Workflow) -> Self {
        Self {
            content: content.to_string(),
            custom_instructions: None,
            workflow,
        }
    }
}
