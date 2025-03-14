use derive_more::derive::From;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::tool_call_parser::parse;
use crate::{Error, Result, ToolName};

/// Unique identifier for a using a tool
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct ToolCallId(pub(crate) String);

impl ToolCallId {
    pub fn new(value: impl ToString) -> Self {
        ToolCallId(value.to_string())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Contains a part message for using a tool. This is received as a part of the
/// response from the model only when streaming is enabled.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize, Setters)]
#[setters(strip_option, into)]
pub struct ToolCallPart {
    /// Optional unique identifier that represents a single call to the tool
    /// use. NOTE: Not all models support a call ID for using a tool
    pub call_id: Option<ToolCallId>,
    pub name: Option<ToolName>,

    /// Arguments that need to be passed to the tool. NOTE: Not all tools
    /// require input
    pub arguments_part: String,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize, From)]
pub enum ToolCall {
    Full(ToolCallFull),
    Part(ToolCallPart),
}

impl ToolCall {
    pub fn as_partial(&self) -> Option<&ToolCallPart> {
        match self {
            ToolCall::Full(_) => None,
            ToolCall::Part(part) => Some(part),
        }
    }

    pub fn as_full(&self) -> Option<&ToolCallFull> {
        match self {
            ToolCall::Full(full) => Some(full),
            ToolCall::Part(_) => None,
        }
    }
}

/// Contains the full information about using a tool. This is received as a part
/// of the response from the model when streaming is disabled.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize, Setters)]
#[setters(strip_option, into)]
#[serde(rename_all = "snake_case")]
pub struct ToolCallFull {
    pub name: ToolName,
    pub call_id: Option<ToolCallId>,
    pub arguments: Value,
}

impl ToolCallFull {
    pub fn new(tool_name: ToolName) -> Self {
        Self { name: tool_name, call_id: None, arguments: Value::default() }
    }

    pub fn try_from_parts(parts: &[ToolCallPart]) -> Result<Vec<Self>> {
        if parts.is_empty() {
            return Ok(vec![]);
        }

        let mut tool_name: Option<&ToolName> = None;
        let mut tool_call_id = None;

        let mut tool_calls = Vec::new();

        let mut input = String::new();
        for part in parts.iter() {
            if let Some(value) = &part.call_id {
                if let Some(tool_name) = tool_name {
                    if !input.is_empty() {
                        // Try to parse the JSON and handle fragmented/incomplete JSON
                        match serde_json::from_str::<Value>(&input) {
                            Ok(json_value) => {
                                tool_calls.push(ToolCallFull {
                                    name: tool_name.clone(),
                                    call_id: tool_call_id,
                                    arguments: json_value,
                                });
                                input.clear();
                            }
                            Err(err) => {
                                // If JSON parsing fails, this might be incomplete/fragmented JSON
                                // Log the error but don't attempt to parse it yet as we might receive more fragments
                                return Err(Error::ToolCallIncompleteArguments(format!(
                                    "Incomplete tool call arguments for {}: {}", 
                                    tool_name.as_str(), 
                                    err
                                )));
                            }
                        }
                    }
                }
                tool_call_id = Some(value.clone());
            }

            if let Some(value) = &part.name {
                tool_name = Some(value);
            }

            input.push_str(&part.arguments_part);
        }

        if !input.is_empty() {
            if let Some(tool_name) = tool_name {
                // Try to parse the JSON and provide a detailed error if it fails
                match serde_json::from_str::<Value>(&input) {
                    Ok(json_value) => {
                        tool_calls.push(ToolCallFull {
                            name: tool_name.clone(),
                            call_id: tool_call_id,
                            arguments: json_value,
                        });
                    }
                    Err(err) => {
                        return Err(Error::ToolCallIncompleteArguments(format!(
                            "Incomplete or malformed tool call arguments for {}: {}\nFragmented JSON: {}", 
                            tool_name.as_str(), 
                            err,
                            input
                        )));
                    }
                }
                input.clear();
            }
        }

        if !tool_calls.is_empty() {
            Ok(tool_calls)
        } else {
            Err(Error::ToolCallMissingName)
        }
    }

    /// Parse multiple tool calls from XML format.
    pub fn try_from_xml(input: &str) -> std::result::Result<Vec<Self>, Error> {
        parse(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_multiple_calls() {
        let input = [
            ToolCallPart {
                call_id: Some(ToolCallId("call_1".to_string())),
                name: Some(ToolName::new("tool_forge_fs_read")),
                arguments_part: "{\"path\": \"crates/forge_app/src/fixtures/mascot.md\"}"
                    .to_string(),
            },
            ToolCallPart {
                call_id: Some(ToolCallId("call_2".to_string())),
                name: Some(ToolName::new("tool_forge_fs_read")),
                arguments_part: "{\"path\": \"docs/onboarding.md\"}".to_string(),
            },
            ToolCallPart {
                call_id: Some(ToolCallId("call_3".to_string())),
                name: Some(ToolName::new("tool_forge_fs_read")),
                arguments_part: "{\"path\": \"crates/forge_app/src/service/service.md\"}"
                    .to_string(),
            },
        ];

        let actual = ToolCallFull::try_from_parts(&input).unwrap();

        let exepected = vec![
            ToolCallFull {
                name: ToolName::new("tool_forge_fs_read"),
                call_id: Some(ToolCallId("call_1".to_string())),
                arguments: serde_json::json!({"path": "crates/forge_app/src/fixtures/mascot.md"}),
            },
            ToolCallFull {
                name: ToolName::new("tool_forge_fs_read"),
                call_id: Some(ToolCallId("call_2".to_string())),
                arguments: serde_json::json!({"path": "docs/onboarding.md"}),
            },
            ToolCallFull {
                name: ToolName::new("tool_forge_fs_read"),
                call_id: Some(ToolCallId("call_3".to_string())),
                arguments: serde_json::json!({"path": "crates/forge_app/src/service/service.md"}),
            },
        ];

        assert_eq!(actual, exepected);
    }

    #[test]
    fn test_single_tool_call() {
        let input = [ToolCallPart {
            call_id: Some(ToolCallId("call_1".to_string())),
            name: Some(ToolName::new("tool_forge_fs_read")),
            arguments_part: "{\"path\": \"docs/onboarding.md\"}".to_string(),
        }];

        let actual = ToolCallFull::try_from_parts(&input).unwrap();
        let expected = vec![ToolCallFull {
            call_id: Some(ToolCallId("call_1".to_string())),
            name: ToolName::new("tool_forge_fs_read"),
            arguments: serde_json::json!({"path": "docs/onboarding.md"}),
        }];

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_empty_call_parts() {
        let actual = ToolCallFull::try_from_parts(&[]).unwrap();
        let expected = vec![];

        assert_eq!(actual, expected);
    }
    #[test]
    fn test_fragmented_json() {
        // Test with a fragmented JSON string where a string value is split
        let input = [
            ToolCallPart {
                call_id: Some(ToolCallId("call_1".to_string())),
                name: Some(ToolName::new("tool_forge_event_dispatch")),
                arguments_part: "{\"id\": \"".to_string(),
            },
            ToolCallPart {
                call_id: None,
                name: None,
                arguments_part: "time_ret".to_string(),
            },
            ToolCallPart {
                call_id: None,
                name: None,
                arguments_part: "rieval\"".to_string(),
            },
        ];

        // With our new implementation, this should now return an ToolCallIncompleteArguments error
        let result = ToolCallFull::try_from_parts(&input);
        assert!(result.is_err());
        if let Err(err) = result {
            match err {
                Error::ToolCallIncompleteArguments(msg) => {
                    assert!(msg.contains("Incomplete"));
                    assert!(msg.contains("tool_forge_event_dispatch"));
                }
                _ => panic!("Expected ToolCallIncompleteArguments error, got {:?}", err),
            }
        }
    }

    #[test]
    fn test_valid_multipart_json() {
        // Test with JSON split into multiple parts but still valid when concatenated
        let input = [
            ToolCallPart {
                call_id: Some(ToolCallId("call_1".to_string())),
                name: Some(ToolName::new("tool_forge_fs_read")),
                arguments_part: "{\"pa".to_string(),
            },
            ToolCallPart {
                call_id: None,
                name: None,
                arguments_part: "th\": \"/h".to_string(),
            },
            ToolCallPart {
                call_id: None,
                name: None,
                arguments_part: "ome/file.txt\"}".to_string(),
            },
        ];

        // With the complete concatenated JSON, this should now parse successfully
        let result = ToolCallFull::try_from_parts(&input);
        
        match result {
            Ok(actual) => {
                let expected = vec![ToolCallFull {
                    call_id: Some(ToolCallId("call_1".to_string())),
                    name: ToolName::new("tool_forge_fs_read"),
                    arguments: serde_json::json!({"path": "/home/file.txt"}),
                }];
                assert_eq!(actual, expected);
            },
            Err(err) => panic!("Expected success but got error: {:?}", err),
        }
    }
}
