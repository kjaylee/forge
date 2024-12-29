use derive_more::derive::{Display, From};
use derive_setters::Setters;
use serde::{Deserialize, Serialize};

use super::{ToolResult, ToolCall};

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
            tool_call: None,
        }
        .into()
    }

    pub fn system(message: impl ToString) -> Self {
        ChatMessage {
            role: ChatRole::System,
            content: message.to_string(),
            tool_call: None,
        }
        .into()
    }

    pub fn assistant(message: impl ToString) -> Self {
        ChatMessage {
            role: ChatRole::Assistant,
            content: message.to_string(),
            tool_call: None,
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

    // FIXME: Message could contain multiple tool calls
    pub tool_call: Option<ToolCall>,
}

impl ChatMessage {
    pub fn assistant(content: impl ToString) -> Self {
        Self {
            role: ChatRole::Assistant,
            content: content.to_string(),
            tool_call: None,
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
