use std::str::FromStr;

use forge_domain::{
    ChatCompletionMessage as ModelResponse, Content, FinishReason, ToolCallFull, ToolCallId,
    ToolCallPart, ToolName,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

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
        error: ErrorResponse,
    },
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ResponseUsage {
    pub prompt_tokens: u64,
    pub completion_tokens: u64,
    pub total_tokens: u64,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
#[serde(untagged)]
pub enum Choice {
    NonChat {
        finish_reason: Option<String>,
        text: String,
        error: Option<ErrorResponse>,
    },
    NonStreaming {
        logprobs: Option<serde_json::Value>,
        index: u32,
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

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ErrorResponse {
    pub code: u32,
    pub message: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<MetaDataError>,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
#[serde(untagged)]
pub enum MetaDataError {
    Moderation {
        reasons: Vec<String>,
        flagged_input: String,
        provider_name: String,
        model_slug: String,
    },
    Provider {
        provider_name: String,
        raw: Value,
    },
    Other(Value),
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
    pub r#type: String,
    pub function: FunctionCall,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct FunctionCall {
    // Only the first event typically has the name of the function call
    pub name: Option<ToolName>,
    pub arguments: String,
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
                                            &tool_call.function.arguments,
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
                                        arguments_part: tool_call.function.arguments.clone(),
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
            OpenRouterResponse::Failure { error } => Err(Error::Upstream {
                message: error.message,
                code: error.code,
                metadata: error
                    .metadata
                    .and_then(|m| serde_json::to_value(m).ok())
                    .filter(|v| !v.is_null()),
            }),
        }
    }
}
