use derive_more::derive::From;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use strum_macros::EnumString;

use super::{ToolCall, ToolCallFull};

#[derive(Default, Clone, Debug, Serialize, PartialEq)]
pub struct Usage {
    pub prompt_tokens: usize,
    pub completion_tokens: usize,
    pub total_tokens: usize,
    pub estimated_tokens: usize,
    pub cached_tokens: usize,
    pub cost: Option<f64>,
}

/// Represents a message that was received from the LLM provider
/// NOTE: Tool call messages are part of the larger Response object and not part
/// of the message.
#[derive(Default, Clone, Debug, Setters, PartialEq)]
#[setters(into, strip_option)]
pub struct ChatCompletionMessage {
    pub content: Option<Content>,
    pub reasoning: Option<Content>,
    pub reasoning_details: Option<Vec<ReasoningDetail>>,
    pub tool_calls: Vec<ToolCall>,
    pub finish_reason: Option<FinishReason>,
    pub usage: Option<Usage>,
}

/// Represents partial or full content of a message
#[derive(Clone, Debug, PartialEq, Eq, From)]
pub enum Content {
    Part(ContentPart),
    Full(ContentFull),
}

impl Content {
    pub fn as_str(&self) -> &str {
        match self {
            Content::Part(part) => &part.0,
            Content::Full(full) => &full.0,
        }
    }

    pub fn part(content: impl ToString) -> Self {
        Content::Part(ContentPart(content.to_string()))
    }

    pub fn full(content: impl ToString) -> Self {
        Content::Full(ContentFull(content.to_string()))
    }

    pub fn is_empty(&self) -> bool {
        self.as_str().is_empty()
    }

    pub fn is_part(&self) -> bool {
        matches!(self, Content::Part(_))
    }
}

/// Represents a reasoning detail that may be included in the response
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq)]
pub struct ReasoningDetailPart {
    pub text: Option<String>,
    pub signature: Option<String>,
}

/// Represents a reasoning detail that may be included in the response
#[derive(Debug, Deserialize, Serialize, Clone, PartialEq)]
pub struct ReasoningDetailFull {
    pub text: Option<String>,
    pub signature: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ReasoningDetail {
    Part(Vec<ReasoningDetailPart>),
    Full(Vec<ReasoningDetailFull>),
}

impl ReasoningDetail {
    pub fn as_partial(&self) -> Option<&Vec<ReasoningDetailPart>> {
        match self {
            ReasoningDetail::Part(parts) => Some(parts),
            ReasoningDetail::Full(_) => None,
        }
    }

    pub fn as_full(&self) -> Option<&Vec<ReasoningDetailFull>> {
        match self {
            ReasoningDetail::Part(_) => None,
            ReasoningDetail::Full(full) => Some(full),
        }
    }

    pub fn from_parts(parts: Vec<Vec<ReasoningDetailPart>>) -> Vec<ReasoningDetailFull> {
        // We merge based on index.
        // eg. [ [a,b,c], [d,e,f], [g,h,i] ] -> [a,d,g], [b,e,h], [c,f,i]
        
        // Find the maximum length of the inner vectors
        let max_length = parts.iter().map(|v| v.len()).max().unwrap_or(0);
        
        // For each index, collect all parts at that index
        (0..max_length)
            .map(|i| {
                let mut merged = ReasoningDetailFull {
                    text: None,
                    signature: None,
                };
                
                // Go through each part vector and get the element at the current index if it exists
                for part_vec in &parts {
                    if i < part_vec.len() {
                        let part = &part_vec[i];
                        
                        // Merge the text
                        if let Some(text) = &part.text {
                            match &mut merged.text {
                                Some(merged_text) => merged_text.push_str(text),
                                None => merged.text = Some(text.clone()),
                            }
                        }
                        
                        // Merge the signature
                        if let Some(signature) = &part.signature {
                            match &mut merged.signature {
                                Some(merged_signature) => merged_signature.push_str(signature),
                                None => merged.signature = Some(signature.clone()),
                            }
                        }
                    }
                }
                
                merged
            })
            .collect()
    }
}

/// Used typically when streaming is enabled
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ContentPart(String);

/// Used typically when full responses are enabled (Streaming is disabled)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ContentFull(String);

/// The reason why the model stopped generating output.
/// Read more: https://platform.openai.com/docs/guides/function-calling#edge-cases
#[derive(Clone, Debug, Deserialize, Serialize, EnumString, PartialEq, Eq)]
pub enum FinishReason {
    /// The model stopped generating output because it reached the maximum
    /// allowed length.
    #[strum(serialize = "length")]
    Length,
    /// The model stopped generating output because it encountered content that
    /// violated filters.
    #[strum(serialize = "content_filter")]
    ContentFilter,
    /// The model stopped generating output because it made a tool call.
    #[strum(serialize = "tool_calls")]
    ToolCalls,
    /// The model stopped generating output normally.
    #[strum(serialize = "stop", serialize = "end_turn")]
    Stop,
}

impl ChatCompletionMessage {
    pub fn assistant(content: impl Into<Content>) -> ChatCompletionMessage {
        ChatCompletionMessage::default().content(content.into())
    }

    pub fn add_reasoning_detail(mut self, detail: impl Into<ReasoningDetail>) -> Self {
        let detail = detail.into();
        if let Some(ref mut details) = self.reasoning_details {
            details.push(detail);
        } else {
            self.reasoning_details = Some(vec![detail]);
        }
        self
    }

    pub fn add_tool_call(mut self, call_tool: impl Into<ToolCall>) -> Self {
        self.tool_calls.push(call_tool.into());
        self
    }

    pub fn extend_calls(mut self, calls: Vec<impl Into<ToolCall>>) -> Self {
        self.tool_calls.extend(calls.into_iter().map(Into::into));
        self
    }

    pub fn finish_reason_opt(mut self, reason: Option<FinishReason>) -> Self {
        self.finish_reason = reason;
        self
    }

    pub fn content_part(mut self, content: impl ToString) -> Self {
        self.content = Some(Content::Part(ContentPart(content.to_string())));
        self
    }

    pub fn content_full(mut self, content: impl ToString) -> Self {
        self.content = Some(Content::Full(ContentFull(content.to_string())));
        self
    }
}

/// Represents a complete message from the LLM provider with all content
/// collected This is typically used after processing a stream of
/// ChatCompletionMessage
#[derive(Clone, Debug, PartialEq)]
pub struct ChatCompletionMessageFull {
    pub content: String,
    pub reasoning: Option<String>,
    pub tool_calls: Vec<ToolCallFull>,
    pub reasoning_details: Option<Vec<ReasoningDetailFull>>,
    pub usage: Usage,
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_reasoning_detail_from_parts() {
        // Create a fixture with three vectors of ReasoningDetailPart
        let fixture = vec![
            // First vector [a, b, c]
            vec![
                ReasoningDetailPart {
                    text: Some("a-text".to_string()),
                    signature: Some("a-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("b-text".to_string()),
                    signature: Some("b-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("c-text".to_string()),
                    signature: Some("c-sig".to_string()),
                },
            ],
            // Second vector [d, e, f]
            vec![
                ReasoningDetailPart {
                    text: Some("d-text".to_string()),
                    signature: Some("d-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("e-text".to_string()),
                    signature: Some("e-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("f-text".to_string()),
                    signature: Some("f-sig".to_string()),
                },
            ],
            // Third vector [g, h, i]
            vec![
                ReasoningDetailPart {
                    text: Some("g-text".to_string()),
                    signature: Some("g-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("h-text".to_string()),
                    signature: Some("h-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("i-text".to_string()),
                    signature: Some("i-sig".to_string()),
                },
            ],
        ];

        // Execute the function to get the actual result
        let actual = ReasoningDetail::from_parts(fixture);

        // Define the expected result
        let expected = vec![
            // First merged vector [a, d, g]
            ReasoningDetailFull {
                text: Some("a-textd-textg-text".to_string()),
                signature: Some("a-sigd-sigg-sig".to_string()),
            },
            // Second merged vector [b, e, h]
            ReasoningDetailFull {
                text: Some("b-texte-texth-text".to_string()),
                signature: Some("b-sige-sigh-sig".to_string()),
            },
            // Third merged vector [c, f, i]
            ReasoningDetailFull {
                text: Some("c-textf-texti-text".to_string()),
                signature: Some("c-sigf-sigi-sig".to_string()),
            },
        ];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reasoning_detail_from_parts_with_different_lengths() {
        // Create a fixture with vectors of different lengths
        let fixture = vec![
            vec![
                ReasoningDetailPart {
                    text: Some("a-text".to_string()),
                    signature: Some("a-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("b-text".to_string()),
                    signature: Some("b-sig".to_string()),
                },
            ],
            vec![
                ReasoningDetailPart {
                    text: Some("c-text".to_string()),
                    signature: Some("c-sig".to_string()),
                },
            ],
            vec![
                ReasoningDetailPart {
                    text: Some("d-text".to_string()),
                    signature: Some("d-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("e-text".to_string()),
                    signature: Some("e-sig".to_string()),
                },
                ReasoningDetailPart {
                    text: Some("f-text".to_string()),
                    signature: Some("f-sig".to_string()),
                },
            ],
        ];

        // Execute the function to get the actual result
        let actual = ReasoningDetail::from_parts(fixture);

        // Define the expected result
        let expected = vec![
            // First merged vector [a, c, d]
            ReasoningDetailFull {
                text: Some("a-textc-textd-text".to_string()),
                signature: Some("a-sigc-sigd-sig".to_string()),
            },
            // Second merged vector [b, e]
            ReasoningDetailFull {
                text: Some("b-texte-text".to_string()),
                signature: Some("b-sige-sig".to_string()),
            },
            // Third merged vector [f]
            ReasoningDetailFull {
                text: Some("f-text".to_string()),
                signature: Some("f-sig".to_string()),
            },
        ];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reasoning_detail_from_parts_with_none_values() {
        // Create a fixture with some None values
        let fixture = vec![
            vec![
                ReasoningDetailPart {
                    text: Some("a-text".to_string()),
                    signature: None,
                },
            ],
            vec![
                ReasoningDetailPart {
                    text: None,
                    signature: Some("b-sig".to_string()),
                },
            ],
        ];

        // Execute the function to get the actual result
        let actual = ReasoningDetail::from_parts(fixture);

        // Define the expected result
        let expected = vec![
            ReasoningDetailFull {
                text: Some("a-text".to_string()),
                signature: Some("b-sig".to_string()),
            },
        ];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reasoning_detail_from_empty_parts() {
        // Empty fixture
        let fixture: Vec<Vec<ReasoningDetailPart>> = vec![];

        // Execute the function to get the actual result
        let actual = ReasoningDetail::from_parts(fixture);

        // Define the expected result - should be an empty vector
        let expected: Vec<ReasoningDetailFull> = vec![];

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_finish_reason_from_str() {
        assert_eq!(
            FinishReason::from_str("length").unwrap(),
            FinishReason::Length
        );
        assert_eq!(
            FinishReason::from_str("content_filter").unwrap(),
            FinishReason::ContentFilter
        );
        assert_eq!(
            FinishReason::from_str("tool_calls").unwrap(),
            FinishReason::ToolCalls
        );
        assert_eq!(FinishReason::from_str("stop").unwrap(), FinishReason::Stop);
        assert_eq!(
            FinishReason::from_str("end_turn").unwrap(),
            FinishReason::Stop
        );
    }
}
