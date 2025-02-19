#![allow(dead_code)]
use std::{
    convert::Infallible,
    fmt::{self, Display, Formatter},
    str::FromStr,
};

use forge_domain::{ChatCompletionMessage, Content, ToolCallId, ToolCallPart, ToolName};
use serde::{Deserialize, Serialize};

use super::request::Role;

#[derive(Deserialize, PartialEq, Clone, Debug)]
pub struct Response {
    pub id: String,
    pub r#type: String,
    pub role: Role,
    pub content: Vec<ContentBlock>,
    pub model: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop_reason: Option<StopReason>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stop_sequence: Option<String>,
    pub usage: Usage,
}

#[derive(Deserialize, PartialEq, Clone, Debug)]
pub struct Usage {
    pub input_tokens: Option<u64>,
    pub output_tokens: Option<u64>,
}

#[derive(Debug, Deserialize, Clone, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum StopReason {
    EndTurn,
    MaxTokens,
    StopSequence,
    ToolUse,
}

impl From<StopReason> for forge_domain::FinishReason {
    fn from(value: StopReason) -> Self {
        match value {
            StopReason::EndTurn => forge_domain::FinishReason::Stop,
            StopReason::MaxTokens => forge_domain::FinishReason::Length,
            StopReason::StopSequence => {
                todo!("not sure about this")
            }
            StopReason::ToolUse => forge_domain::FinishReason::ToolCalls,
        }
    }
}

#[derive(Debug, Deserialize, Clone, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum EventName {
    Unspecified,
    Error,
    MessageStart,
    ContentBlockStart,
    Ping,
    ContentBlockDelta,
    ContentBlockStop,
    MessageDelta,
    MessageStop,
}

impl FromStr for EventName {
    type Err = Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "error" => Ok(EventName::Error),
            "message_start" => Ok(EventName::MessageStart),
            "content_block_start" => Ok(EventName::ContentBlockStart),
            "ping" => Ok(EventName::Ping),
            "content_block_delta" => Ok(EventName::ContentBlockDelta),
            "content_block_stop" => Ok(EventName::ContentBlockStop),
            "message_delta" => Ok(EventName::MessageDelta),
            "message_stop" => Ok(EventName::MessageStop),
            _ => Ok(EventName::Unspecified),
        }
    }
}

#[derive(Deserialize, PartialEq, Clone, Debug)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum EventData {
    Error {
        error: ErrorData,
    },
    MessageStart {
        message: Response,
    },
    ContentBlockStart {
        index: u32,
        content_block: ContentBlock,
    },
    Ping,
    ContentBlockDelta {
        index: u32,
        delta: ContentBlock,
    },
    ContentBlockStop {
        index: u32,
    },
    MessageDelta {
        delta: MessageDelta,
        usage: Usage,
    },
    MessageStop,
}

#[derive(Debug, Deserialize, Clone, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum ErrorData {
    OverloadedError { message: String },
}

impl Display for ErrorData {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorData::OverloadedError { message } => write!(f, "OverloadedError: {}", message),
        }
    }
}

#[derive(Deserialize, Clone, PartialEq, Debug)]
pub struct MessageDelta {
    pub stop_reason: StopReason,
    pub stop_sequence: Option<String>,
}

#[derive(Debug, Deserialize, Clone, PartialEq)]
#[serde(tag = "type")]
#[serde(rename_all = "snake_case")]
pub enum ContentBlock {
    Text {
        text: String,
    },
    Image {
        source: ImageSource,
    },
    TextDelta {
        text: String,
    },
    ToolUse {
        id: String,
        name: String,
        input: serde_json::Value,
    },
    ToolResult {
        tool_use_id: String,
        content: String,
    },
    InputJsonDelta {
        partial_json: String,
    },
}

impl ContentBlock {
    pub fn is_empty(&self) -> bool {
        match self {
            ContentBlock::Text { text } => text.trim().is_empty(),
            ContentBlock::Image { source } => match source {
                ImageSource::Base64 { media_type, data } => {
                    media_type.trim().is_empty() || data.trim().is_empty()
                }
            },
            ContentBlock::TextDelta { text } => text.trim().is_empty(),
            ContentBlock::ToolUse { id, name, input } => {
                id.is_empty() || name.is_empty() || input.is_null()
            }
            ContentBlock::ToolResult { tool_use_id, content } => {
                tool_use_id.is_empty() || content.is_empty()
            }
            ContentBlock::InputJsonDelta { partial_json } => partial_json.is_empty(),
        }
    }
}

#[derive(Debug, Deserialize, Clone, PartialEq, Serialize)]
#[serde(tag = "type")]
pub enum ImageSource {
    #[serde(rename = "base64")]
    Base64 { media_type: String, data: String },
}

impl TryFrom<EventData> for ChatCompletionMessage {
    type Error = anyhow::Error;
    fn try_from(value: EventData) -> Result<Self, Self::Error> {
        let result = match value {
            EventData::ContentBlockStart { content_block, .. }
            | EventData::ContentBlockDelta { delta: content_block, .. } => {
                ChatCompletionMessage::try_from(content_block)?
            }
            EventData::MessageDelta { delta, usage: _usage } => {
                ChatCompletionMessage::assistant(Content::part("")).finish_reason(delta.stop_reason)
            }
            EventData::MessageStart { message: _message } => {
                ChatCompletionMessage::assistant(Content::part(""))
            }
            EventData::Error { error } => {
                return Err(anyhow::anyhow!("Anthropic API error: {}", error));
            }
            _ => ChatCompletionMessage::assistant(Content::part("")),
        };

        Ok(result)
    }
}

impl TryFrom<ContentBlock> for ChatCompletionMessage {
    type Error = anyhow::Error;
    fn try_from(value: ContentBlock) -> Result<Self, Self::Error> {
        match value {
            ContentBlock::Image { source: _source } => todo!("Image not supported"),
            ContentBlock::Text { text } | ContentBlock::TextDelta { text } => {
                Ok(ChatCompletionMessage::assistant(Content::part(text)))
            }
            ContentBlock::ToolUse { id, name, input } => Ok(ChatCompletionMessage::assistant(
                Content::part(""),
            )
            .add_tool_call(ToolCallPart {
                call_id: Some(ToolCallId::new(id)),
                name: Some(ToolName::new(name)),
                arguments_part: serde_json::to_string(&input)?,
            })),
            ContentBlock::InputJsonDelta { partial_json } => {
                Ok(
                    ChatCompletionMessage::assistant(Content::part("")).add_tool_call(
                        ToolCallPart { call_id: None, name: None, arguments_part: partial_json },
                    ),
                )
            }
            _ => Ok(ChatCompletionMessage::assistant(Content::part(""))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serde() {
        let tests = vec![
            (
                "error",
                r#"{"type": "error", "error": {"type": "overloaded_error", "message": "Overloaded"}}"#,
                EventName::Error,
                EventData::Error {
                    error: ErrorData::OverloadedError { message: "Overloaded".to_string() },
                },
            ),
            (
                "message_start",
                r#"{"type":"message_start","message":{"id":"msg_019LBLYFJ7fG3fuAqzuRQbyi","type":"message","role":"assistant","content":[],"model":"claude-3-opus-20240229","stop_reason":null,"stop_sequence":null,"usage":{"input_tokens":10,"output_tokens":1}}}"#,
                EventName::MessageStart,
                EventData::MessageStart {
                    message: Response {
                        id: "msg_019LBLYFJ7fG3fuAqzuRQbyi".to_string(),
                        r#type: "message".to_string(),
                        role: Role::Assistant,
                        content: vec![],
                        model: "claude-3-opus-20240229".to_string(),
                        stop_reason: None,
                        stop_sequence: None,
                        usage: Usage { input_tokens: Some(10), output_tokens: Some(1) },
                    },
                },
            ),
            (
                "content_block_start",
                r#"{"type":"content_block_start","index":0,"content_block":{"type":"text","text":""}}"#,
                EventName::ContentBlockStart,
                EventData::ContentBlockStart {
                    index: 0,
                    content_block: ContentBlock::Text { text: "".to_string() },
                },
            ),
            (
                "ping",
                r#"{"type": "ping"}"#,
                EventName::Ping,
                EventData::Ping,
            ),
            (
                "content_block_delta",
                r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Hello"}}"#,
                EventName::ContentBlockDelta,
                EventData::ContentBlockDelta {
                    index: 0,
                    delta: ContentBlock::TextDelta { text: "Hello".to_string() },
                },
            ),
            (
                "content_block_delta",
                r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"!"}}"#,
                EventName::ContentBlockDelta,
                EventData::ContentBlockDelta {
                    index: 0,
                    delta: ContentBlock::TextDelta { text: "!".to_string() },
                },
            ),
            (
                "content_block_stop",
                r#"{"type":"content_block_stop","index":0}"#,
                EventName::ContentBlockStop,
                EventData::ContentBlockStop { index: 0 },
            ),
            (
                "message_delta",
                r#"{"type":"message_delta","delta":{"stop_reason":"end_turn","stop_sequence":null},"usage":{"output_tokens":12}}"#,
                EventName::MessageDelta,
                EventData::MessageDelta {
                    delta: MessageDelta { stop_reason: StopReason::EndTurn, stop_sequence: None },
                    usage: Usage { input_tokens: None, output_tokens: Some(12) },
                },
            ),
            (
                "message_stop",
                r#"{"type":"message_stop"}"#,
                EventName::MessageStop,
                EventData::MessageStop,
            ),
        ];
        for (name, input, event_name, event_data) in tests {
            let got_event_name = EventName::from_str(name).unwrap();
            assert_eq!(
                got_event_name, event_name,
                "test failed for event name: {}",
                name
            );

            let got: EventData = serde_json::from_str(input).unwrap();
            assert_eq!(got, event_data, "test failed for event data: {}", name);
        }
    }
}
