use std::fmt;

use serde::Serialize;

/// Represents the type of SSE event to be sent
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum SseEventType {
    Message,
    Error,
}

impl fmt::Display for SseEventType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SseEventType::Message => write!(f, "message"),
            SseEventType::Error => write!(f, "error"),
        }
    }
}

/// The message type for SSE responses
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum MessageType {
    Text,
    ToolCallStart,
    ToolCallEnd,
    Usage,
    Event,
}

/// Represents a serializable SSE message structure
#[derive(Debug, Clone, Serialize)]
pub struct SseMessage {
    pub agent: String,
    #[serde(rename = "type")]
    pub message_type: MessageType,
    pub data: serde_json::Value,
}

/// Represents a serializable SSE error structure
#[derive(Debug, Clone, Serialize)]
pub struct SseError {
    pub error: String,
}
