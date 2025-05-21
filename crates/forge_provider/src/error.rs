use std::collections::BTreeMap;
use std::fmt::Formatter;

use derive_more::derive::Display;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Display, derive_more::From, Error)]
pub enum Error {
    #[display("OpenAI API Error: {_0}")]
    Response(ResponseError),
    #[display("Anthropic API Error: {_0}")]
    Anthropic(AnthropicApiError),
    SerdeJson(serde_json::Error),
    ToolCallMissingName,
    InvalidStatusCode(u16),
}

#[derive(Debug, Display, Deserialize, Serialize, Clone, PartialEq)]
#[serde(untagged)]
pub enum ErrorCode {
    String(String),
    Number(u16),
}

impl ErrorCode {
    pub fn as_number(&self) -> Option<u16> {
        match self {
            ErrorCode::String(s) => s.parse::<u16>().ok(),
            ErrorCode::Number(code) => Some(*code),
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            ErrorCode::String(s) => Some(s),
            ErrorCode::Number(_) => None,
        }
    }
}

#[derive(Default, Debug, Deserialize, Serialize, Clone, Setters)]
pub struct ResponseError {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<Box<ResponseError>>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub errno: Option<i32>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<ErrorCode>,

    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub metadata: BTreeMap<String, serde_json::Value>,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub syscall: Option<String>,

    #[serde(rename = "type", skip_serializing_if = "Option::is_none")]
    pub type_of: Option<serde_json::Value>,

    #[serde(skip_serializing_if = "Option::is_none")]
    pub param: Option<serde_json::Value>,
}

impl ResponseError {
    /// Deeply introspects the error structure to determine the ErrorCode
    pub fn get_code_deep(&self) -> Option<&ErrorCode> {
        if let Some(ref code) = self.code {
            return Some(code);
        }
        if let Some(ref error) = self.error {
            return error.get_code_deep();
        }
        None
    }
}

impl std::fmt::Display for ResponseError {
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

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_error_code_as_number() {
        // Test with numeric error code
        let code_number = ErrorCode::Number(404);
        assert_eq!(code_number.as_number(), Some(404));

        // Test with string error code containing a valid number
        let code_string_numeric = ErrorCode::String("500".to_string());
        assert_eq!(code_string_numeric.as_number(), Some(500));

        // Test with string error code containing a non-numeric value
        let code_string_non_numeric = ErrorCode::String("ERR_STREAM_PREMATURE_CLOSE".to_string());
        assert_eq!(code_string_non_numeric.as_number(), None);
    }

    #[test]
    fn test_error_code_as_str() {
        // Test with string error code
        let code_string = ErrorCode::String("ERR_STREAM_PREMATURE_CLOSE".to_string());
        assert_eq!(code_string.as_str(), Some("ERR_STREAM_PREMATURE_CLOSE"));

        // Test with numeric error code
        let code_number = ErrorCode::Number(404);
        assert_eq!(code_number.as_str(), None);
    }

    #[test]
    fn test_get_code_deep_direct() {
        // Test with an error that has a direct code
        let error_code = ErrorCode::Number(404);

        // Use derived setters for a cleaner initialization
        let fixture = ResponseError::default()
            .message(Some("Error message".to_string()))
            .code(Some(error_code));

        let actual = fixture.get_code_deep();

        // Create a new ErrorCode to compare against
        let expected_code = ErrorCode::Number(404);
        assert_eq!(actual, Some(&expected_code));
    }

    #[test]
    fn test_get_code_deep_nested() {
        // Test with an error that has no direct code but has an inner error with a code
        let error_code = ErrorCode::String("ERR_STREAM_PREMATURE_CLOSE".to_string());

        // Use derived setters for cleaner initialization
        let inner_error = ResponseError::default()
            .message(Some("Inner error".to_string()))
            .code(Some(error_code));

        let fixture = ResponseError::default()
            .error(Some(Box::new(inner_error)))
            .message(Some("Outer error".to_string()));

        let actual = fixture.get_code_deep();

        // Create a new ErrorCode to compare against
        let expected_code = ErrorCode::String("ERR_STREAM_PREMATURE_CLOSE".to_string());
        assert_eq!(actual, Some(&expected_code));
    }

    #[test]
    fn test_get_code_deep_no_code() {
        // Test with an error that has no code and no inner error
        let fixture = ResponseError::default().message(Some("Error message".to_string()));

        let actual = fixture.get_code_deep();
        let expected = None;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_get_code_deep_multiple_nested() {
        // Test with deeply nested errors
        let error_code = ErrorCode::Number(500);

        let deepest_error = ResponseError::default()
            .message(Some("Deepest error".to_string()))
            .code(Some(error_code));

        let middle_error = ResponseError::default()
            .error(Some(Box::new(deepest_error)))
            .message(Some("Middle error".to_string()));
        // No code here, should find deepest

        let fixture = ResponseError::default()
            .error(Some(Box::new(middle_error)))
            .message(Some("Outer error".to_string()));
        // No code here, should find deepest

        let actual = fixture.get_code_deep();

        // Create a new ErrorCode to compare against
        let expected_code = ErrorCode::Number(500);
        assert_eq!(actual, Some(&expected_code));
    }
}
