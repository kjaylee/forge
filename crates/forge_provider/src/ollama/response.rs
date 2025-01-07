use forge_domain::{ChatCompletionMessage, Content, ModelId};
use serde::Deserialize;

use crate::error::Error;

#[derive(Debug, Deserialize)]
pub struct ChatResponse {
    pub model: String,
    pub created_at: String,
    pub message: ResponseMessage,
    pub done: bool,
}

#[derive(Debug, Deserialize)]
pub struct ResponseMessage {
    pub role: String,
    pub content: String,
}

impl TryFrom<ChatResponse> for ChatCompletionMessage {
    type Error = Error;

    fn try_from(response: ChatResponse) -> Result<Self, Error> {
        Ok(ChatCompletionMessage::assistant(Content::part(
            response.message.content,
        )))
    }
}

// Models response
#[derive(Debug, Deserialize)]
pub struct ModelsResponse {
    pub models: Vec<ModelInfo>,
}

#[derive(Debug, Deserialize)]
pub struct ModelInfo {
    pub name: ModelId,
    pub modified_at: String,
    pub size: u64,
    pub digest: String,
}
