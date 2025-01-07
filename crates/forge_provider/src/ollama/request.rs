use forge_domain::{Context, ContextMessage, ModelId};
use serde::Serialize;

use super::model::{OllamaMessage, OllamaParameters};
use crate::error::{Error, Result};

#[derive(Debug, Serialize)]
pub struct ChatRequest {
    pub model: ModelId,
    pub messages: Vec<OllamaMessage>,
    pub stream: bool,
    #[serde(flatten)]
    pub options: OllamaParameters,
}

impl TryFrom<Context> for ChatRequest {
    type Error = Error;

    fn try_from(context: Context) -> Result<Self> {
        let model = context.model;
        let messages = context.messages.into_iter().map(convert_message).collect();

        Ok(ChatRequest {
            model,
            messages,
            stream: true,
            options: OllamaParameters { temperature: None, top_p: None, top_k: None },
        })
    }
}

fn convert_message(message: ContextMessage) -> OllamaMessage {
    match message {
        ContextMessage::ContentMessage(msg) => OllamaMessage {
            role: msg.role.to_string().to_lowercase(),
            content: msg.content,
        },
        ContextMessage::ToolMessage(result) => OllamaMessage {
            role: "assistant".to_string(),
            content: format!(
                "Tool result: {}",
                serde_json::to_string(&result.content).unwrap()
            ),
        },
    }
}
