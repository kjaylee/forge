use std::collections::HashMap;
use std::str::FromStr;

use forge_domain::{
    ChatCompletionMessage as ModelResponse, Content, FinishReason, ToolCallFull, ToolCallId,
    ToolCallPart, ToolName,
};
use serde::{Deserialize, Serialize};

use super::tool_choice::FunctionType;
use crate::error::Error;

#[derive(Debug, Deserialize, Serialize, Clone)]
#[serde(untagged)]
pub enum OpenRouterResponse {
    Success {
        id: String,
        provider: String,
        model: String,
        choices: Vec<Choice>,
        created: u64,
        object: String,
        system_fingerprint: Option<String>,
        usage: Option<ResponseUsage>,
    },
    Failure {
        error: OpenRouterErrorResponse,
    },
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenRouterErrorResponse {
    code: u32,
    message: String,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ResponseUsage {
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub total_tokens: u64,
}

#[derive(Debug, Serialize, Clone)]
pub enum Choice {
    NonChat {
        finish_reason: Option<String>,
        text: String,
        error: Option<ErrorResponse>,
    },
    NonStreaming {
        finish_reason: Option<String>,
        message: ResponseMessage,
        error: Option<ErrorResponse>,
    },
    Streaming {
        finish_reason: Option<String>,
        delta: ResponseMessage,
        error: Option<ErrorResponse>,
    },
}

// note:
// Custom deserialization is needed for the Choice enum because:
// 1. The streaming response JSON contains overlapping fields (error,
//    finish_reason) that exist in multiple variants
// 2. Using #[serde(untagged)] causes serde to match the first variant whose
//    fields are all present in the JSON
// 3. Since all variants have 'error' and 'finish_reason', untagged
//    deserialization incorrectly chooses NonChat even when 'delta' field is
//    present
impl<'de> Deserialize<'de> for Choice {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let value = serde_json::Value::deserialize(deserializer)?;
        let obj = value
            .as_object()
            .ok_or_else(|| serde::de::Error::custom("expected an object"))?;

        if obj.contains_key("delta") {
            // Parse as Streaming variant
            Ok(Choice::Streaming {
                finish_reason: obj
                    .get("finish_reason")
                    .and_then(|v| v.as_str())
                    .map(String::from),
                delta: serde_json::from_value(
                    obj.get("delta")
                        .ok_or_else(|| serde::de::Error::custom("missing delta field"))?
                        .clone(),
                )
                .map_err(serde::de::Error::custom)?,
                error: obj
                    .get("error")
                    .map(|v| serde_json::from_value(v.clone()))
                    .transpose()
                    .map_err(serde::de::Error::custom)?,
            })
        } else if obj.contains_key("message") {
            // Parse as NonStreaming variant
            Ok(Choice::NonStreaming {
                finish_reason: obj
                    .get("finish_reason")
                    .and_then(|v| v.as_str())
                    .map(String::from),
                message: serde_json::from_value(
                    obj.get("message")
                        .ok_or_else(|| serde::de::Error::custom("missing message field"))?
                        .clone(),
                )
                .map_err(serde::de::Error::custom)?,
                error: obj
                    .get("error")
                    .map(|v| serde_json::from_value(v.clone()))
                    .transpose()
                    .map_err(serde::de::Error::custom)?,
            })
        } else {
            // Parse as NonChat variant
            Ok(Choice::NonChat {
                finish_reason: obj
                    .get("finish_reason")
                    .and_then(|v| v.as_str())
                    .map(String::from),
                text: obj
                    .get("text")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| serde::de::Error::custom("missing text field"))?
                    .to_string(),
                error: obj
                    .get("error")
                    .map(|v| serde_json::from_value(v.clone()))
                    .transpose()
                    .map_err(serde::de::Error::custom)?,
            })
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ErrorResponse {
    pub code: u32,
    pub message: String,
    pub metadata: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ResponseMessage {
    pub content: Option<String>,
    pub role: Option<String>,
    pub tool_calls: Option<Vec<OpenRouterToolCall>>,
    pub refusal: Option<String>,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct OpenRouterToolCall {
    pub id: Option<ToolCallId>,
    pub r#type: FunctionType,
    pub function: FunctionCall,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct FunctionCall {
    // Only the first event typically has the name of the function call
    pub name: Option<ToolName>,
    pub arguments: Option<String>,
}

impl TryFrom<OpenRouterResponse> for ModelResponse {
    type Error = Error;

    fn try_from(res: OpenRouterResponse) -> Result<Self, Self::Error> {
        match res {
            OpenRouterResponse::Success { choices, .. } => {
                if let Some(choice) = choices.first() {
                    let response = match choice {
                        Choice::NonChat { text, finish_reason, .. } => {
                            ModelResponse::assistant(Content::full(text)).finish_reason_opt(
                                finish_reason
                                    .clone()
                                    .and_then(|s| FinishReason::from_str(&s).ok()),
                            )
                        }
                        Choice::NonStreaming { message, finish_reason, .. } => {
                            let mut resp = ModelResponse::assistant(Content::full(
                                message.content.clone().unwrap_or_default(),
                            ))
                            .finish_reason_opt(
                                finish_reason
                                    .clone()
                                    .and_then(|s| FinishReason::from_str(&s).ok()),
                            );
                            if let Some(tool_calls) = &message.tool_calls {
                                for tool_call in tool_calls {
                                    resp = resp.add_tool_call(ToolCallFull {
                                        call_id: tool_call.id.clone(),
                                        name: tool_call
                                            .function
                                            .name
                                            .clone()
                                            .ok_or(Error::ToolCallMissingName)?,
                                        arguments: serde_json::from_str(
                                            &tool_call
                                                .function
                                                .arguments
                                                .clone()
                                                .unwrap_or_default(),
                                        )?,
                                    });
                                }
                            }
                            resp
                        }
                        Choice::Streaming { delta, finish_reason, .. } => {
                            let mut resp = ModelResponse::assistant(Content::part(
                                delta.content.clone().unwrap_or_default(),
                            ))
                            .finish_reason_opt(
                                finish_reason
                                    .clone()
                                    .and_then(|s| FinishReason::from_str(&s).ok()),
                            );
                            if let Some(tool_calls) = &delta.tool_calls {
                                for tool_call in tool_calls {
                                    resp = resp.add_tool_call(ToolCallPart {
                                        call_id: tool_call.id.clone(),
                                        name: tool_call.function.name.clone(),
                                        arguments_part: tool_call
                                            .function
                                            .arguments
                                            .clone()
                                            .unwrap_or_default(),
                                    });
                                }
                            }
                            resp
                        }
                    };

                    Ok(response)
                } else {
                    Err(Error::EmptyContent)
                }
            }
            OpenRouterResponse::Failure { error } => {
                Err(Error::Upstream { message: error.message, code: error.code })
            }
        }
    }
}
