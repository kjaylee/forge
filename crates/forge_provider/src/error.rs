use std::collections::HashMap;
use std::fmt::Formatter;

use derive_more::derive::Display;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Display, derive_more::From, Error)]
pub enum Error {
    EmptyContent,
    #[display("OpenAI API Error: {_0}")]
    OpenAI(OpenAiApiError),
    #[display("Anthropic API Error: {_0}")]
    Anthropic(AnthropicApiError),
    SerdeJson(serde_json::Error),
    ToolCallMissingName,
    Reqwest(reqwest_eventsource::Error),
    #[display("Invalid Status Code: {_0}")]
    InvalidStatusCode(u16),
}

#[derive(Debug, Display, Deserialize, Serialize, Clone)]
#[serde(untagged)]
pub enum Code {
    String(String),
    Number(u32),
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenAiApiError {
    pub code: Option<Code>,
    pub message: Option<String>,
    #[serde(default, skip_serializing_if = "HashMap::is_empty")]
    pub metadata: HashMap<String, serde_json::Value>,
}

impl std::fmt::Display for OpenAiApiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut output = Vec::new();

        if let Some(ref code) = self.code {
            output.push(format!("code: {code}"));
        }
        if let Some(ref message) = self.message {
            output.push(format!("message: {message}"));
        }
        if !self.metadata.is_empty() {
            if let Ok(str_repr) = serde_json::to_string(&self.metadata) {
                output.push(format!("metadata: {str_repr}"));
            }
        }

        write!(f, "{}", output.join(", "))
    }
}

#[derive(Debug, Deserialize, Clone, PartialEq)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum AnthropicApiError {
    OverloadedError { message: String },
}

impl std::fmt::Display for AnthropicApiError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            AnthropicApiError::OverloadedError { message } => {
                write!(f, "OverloadedError: {message}")
            }
        }
    }
}
