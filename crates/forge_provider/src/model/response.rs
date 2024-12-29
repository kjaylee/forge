use derive_setters::Setters;
use serde::{Deserialize, Serialize};

use super::ToolUsePart;

/// Represents a message that was received from the LLM provider
/// NOTE: ToolUse messages are part of the larger Response object and not part
/// of the message.
#[derive(Clone, Debug, Setters)]
#[setters(into, strip_option)]
pub struct Response {
    pub message: String,
    pub tool_use: Vec<ToolUsePart>,
    pub finish_reason: Option<FinishReason>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum FinishReason {
    ToolUse,
    EndTurn,
}

impl FinishReason {
    pub fn parse(reason: String) -> Option<Self> {
        match reason.as_str() {
            "tool_use" => Some(FinishReason::ToolUse),
            "tool_calls" => Some(FinishReason::ToolUse),
            "end_turn" => Some(FinishReason::EndTurn),
            _ => None,
        }
    }
}

impl Response {
    pub fn assistant(content: impl ToString) -> Response {
        Response::new(content)
    }

    pub fn new(message: impl ToString) -> Response {
        Response {
            message: message.to_string(),
            tool_use: vec![],
            finish_reason: None,
        }
    }

    pub fn add_tool_use(mut self, call_tool: impl Into<ToolUsePart>) -> Self {
        self.tool_use.push(call_tool.into());
        self
    }

    pub fn extend_calls(mut self, calls: Vec<impl Into<ToolUsePart>>) -> Self {
        self.tool_use.extend(calls.into_iter().map(Into::into));
        self
    }

    pub fn finish_reason_opt(mut self, reason: Option<FinishReason>) -> Self {
        self.finish_reason = reason;
        self
    }
}
