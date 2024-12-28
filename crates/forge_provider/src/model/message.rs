use derive_more::derive::{Display, From};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, From, PartialEq, Serialize)]
pub enum Message {
    Response(ResponseMessage),
    Request(RequestMessage),
}

/// Represents a message that was received from the LLM provider
/// NOTE: ToolUse messages are part of the larger Response object and not part
/// of the message.
#[derive(Clone, Debug, Deserialize, From, PartialEq, Serialize)]
pub struct ResponseMessage {
    pub content: String,
}

impl ResponseMessage {
    pub fn assistant(message: impl ToString) -> Self {
        ResponseMessage { content: message.to_string() }
    }
}

impl RequestMessage {
    pub fn user(message: impl ToString) -> Self {
        RequestMessage { role: ChatRole::User, content: message.to_string() }
    }

    pub fn system(message: impl ToString) -> Self {
        RequestMessage { role: ChatRole::System, content: message.to_string() }
    }

    pub fn assistant(message: impl ToString) -> Self {
        RequestMessage { role: ChatRole::Assistant, content: message.to_string() }
    }
}

/// Represents a message being sent to the LLM provider
/// NOTE: ToolResults message are part of the larger Request object and not part
/// of the message.
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub struct RequestMessage {
    pub role: ChatRole,
    pub content: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
pub enum ChatRole {
    System,
    User,
    Assistant,
}

impl From<ChatRole> for Role {
    fn from(role: ChatRole) -> Self {
        match role {
            ChatRole::System => Role::System,
            ChatRole::User => Role::User,
            ChatRole::Assistant => Role::Assistant,
        }
    }
}

#[derive(Debug, Deserialize, Display, Serialize, Clone)]
pub enum Role {
    System,
    User,
    Assistant,
    Tool,
}
