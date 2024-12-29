use derive_more::derive::{Display, From};
use derive_setters::Setters;
use serde::{Deserialize, Serialize};

use super::{ToolResult, ToolUse};

#[derive(Clone, Debug, Deserialize, From, PartialEq, Serialize)]
pub enum Message {
    Response(ResponseMessage),
    Request(ChatMessage),
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

/// Represents a message being sent to the LLM provider
/// NOTE: ToolResults message are part of the larger Request object and not part
/// of the message.
#[derive(Clone, Debug, Deserialize, From, PartialEq, Serialize)]
pub enum RequestMessage {
    Chat(ChatMessage),
    ToolResult(ToolResult),
}

impl RequestMessage {
    pub fn user(message: impl ToString) -> Self {
        ChatMessage {
            role: ChatRole::User,
            content: message.to_string(),
            tool_use: None,
        }
        .into()
    }

    pub fn system(message: impl ToString) -> Self {
        ChatMessage {
            role: ChatRole::System,
            content: message.to_string(),
            tool_use: None,
        }
        .into()
    }

    pub fn assistant(message: impl ToString) -> Self {
        ChatMessage {
            role: ChatRole::Assistant,
            content: message.to_string(),
            tool_use: None,
        }
        .into()
    }

    pub fn content(&self) -> String {
        match self {
            RequestMessage::Chat(message) => message.content.to_string(),
            RequestMessage::ToolResult(result) => serde_json::to_string(&result.content).unwrap(),
        }
    }

    pub fn role(&self) -> Role {
        match self {
            RequestMessage::Chat(message) => message.role.clone().into(),
            RequestMessage::ToolResult(_) => Role::Tool,
        }
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, Setters)]
#[setters(strip_option, into)]
pub struct ChatMessage {
    pub role: ChatRole,
    pub content: String,
    pub tool_use: Option<ToolUse>,
}

impl ChatMessage {
    pub fn assistant(content: impl ToString) -> Self {
        Self {
            role: ChatRole::Assistant,
            content: content.to_string(),
            tool_use: None,
        }
    }
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

#[derive(Debug, Deserialize, Display, Serialize, Clone, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    System,
    User,
    Assistant,
    Tool,
}
