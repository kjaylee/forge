use std::ops::Deref;

use chrono::{DateTime, Utc};
use convert_case::{Case, Casing};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Event {
    pub event_name: Name,
    pub event_value: String,
    pub start_time: DateTime<Utc>,
    pub cores: usize,
    pub client_id: String,
    pub os_name: String,
    pub up_time: i64,
    pub path: Option<String>,
    pub cwd: Option<String>,
    pub user: String,
    pub args: Vec<String>,
    pub version: String,
    pub email: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Name(String);
impl From<String> for Name {
    fn from(name: String) -> Self {
        Self(name.to_case(Case::Snake))
    }
}
impl Deref for Name {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Name> for String {
    fn from(val: Name) -> Self {
        val.0
    }
}

/// Detailed information about an error event
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorDetails {
    /// Categorization of the error (e.g., "NetworkError", "ValidationError")
    pub error_type: String,
    /// Human-readable error message
    pub message: String,
    /// Where the error occurred (module, function, etc.)
    pub context: String,
    /// Optional stack trace if available
    pub stack_trace: Option<String>,
}

#[derive(Debug, Clone)]
pub enum EventKind {
    Start,
    Ping,
    Prompt(String),
    Error(String),
    ErrorOccurred(ErrorDetails),
}

impl EventKind {
    pub fn name(&self) -> Name {
        match self {
            Self::Start => Name::from("start".to_string()),
            Self::Ping => Name::from("ping".to_string()),
            Self::Prompt(_) => Name::from("prompt".to_string()),
            Self::Error(_) => Name::from("error".to_string()),
            Self::ErrorOccurred(_) => Name::from("error_occurred".to_string()),
        }
    }

    pub fn value(&self) -> String {
        match self {
            Self::Start => "".to_string(),
            Self::Ping => "".to_string(),
            Self::Prompt(content) => content.to_string(),
            Self::Error(content) => content.to_string(),
            Self::ErrorOccurred(details) => {
                // Serialize ErrorDetails to JSON
                serde_json::to_string(details)
                    .unwrap_or_else(|_| "Error serializing error details".to_string())
            }
        }
    }

    /// Create a new error event with the specified details
    pub fn error(error_type: &str, message: &str, context: &str) -> Self {
        Self::ErrorOccurred(ErrorDetails {
            error_type: error_type.to_string(),
            message: message.to_string(),
            context: context.to_string(),
            stack_trace: None,
        })
    }

    /// Create a new error event with stack trace included
    pub fn error_with_trace(
        error_type: &str,
        message: &str,
        context: &str,
        stack_trace: String,
    ) -> Self {
        Self::ErrorOccurred(ErrorDetails {
            error_type: error_type.to_string(),
            message: message.to_string(),
            context: context.to_string(),
            stack_trace: Some(stack_trace),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{ErrorDetails, EventKind};

    #[test]
    fn test_error_details_serialization() {
        let error_details = ErrorDetails {
            error_type: "NetworkError".to_string(),
            message: "Failed to connect to server".to_string(),
            context: "forge_main::api::fetch".to_string(),
            stack_trace: Some("Error: Failed to connect...\n  at fetch_data (...)".to_string()),
        };

        let json = serde_json::to_string(&error_details).unwrap();
        let parsed: ErrorDetails = serde_json::from_str(&json).unwrap();

        assert_eq!(parsed.error_type, "NetworkError");
        assert_eq!(parsed.message, "Failed to connect to server");
        assert_eq!(parsed.context, "forge_main::api::fetch");
        assert_eq!(
            parsed.stack_trace,
            Some("Error: Failed to connect...\n  at fetch_data (...)".to_string())
        );
    }

    #[test]
    fn test_error_kind_name() {
        let error_kind = EventKind::ErrorOccurred(ErrorDetails {
            error_type: "ValidationError".to_string(),
            message: "Invalid input".to_string(),
            context: "forge_main::validator::validate".to_string(),
            stack_trace: None,
        });

        let name = error_kind.name();
        assert_eq!(&*name, "error_occurred");
    }

    #[test]
    fn test_error_kind_value() {
        let error_details = ErrorDetails {
            error_type: "DataError".to_string(),
            message: "Missing required field".to_string(),
            context: "forge_main::data::process".to_string(),
            stack_trace: None,
        };

        let error_kind = EventKind::ErrorOccurred(error_details);
        let value = error_kind.value();

        // Parse the value as JSON to verify it contains the expected fields
        let parsed: serde_json::Value = serde_json::from_str(&value).unwrap();

        assert_eq!(parsed["error_type"], "DataError");
        assert_eq!(parsed["message"], "Missing required field");
        assert_eq!(parsed["context"], "forge_main::data::process");
        assert!(parsed["stack_trace"].is_null());
    }

    #[test]
    fn test_error_helper_methods() {
        // Test error helper without stack trace
        let error1 = EventKind::error("FileError", "File not found", "forge_main::fs::read");
        if let EventKind::ErrorOccurred(details) = error1 {
            assert_eq!(details.error_type, "FileError");
            assert_eq!(details.message, "File not found");
            assert_eq!(details.context, "forge_main::fs::read");
            assert_eq!(details.stack_trace, None);
        } else {
            panic!("Expected ErrorOccurred variant");
        }

        // Test error helper with stack trace
        let stack_trace =
            "FileNotFoundError: unable to open file\n  at read_file (...)".to_string();
        let error2 = EventKind::error_with_trace(
            "FileError",
            "File not found",
            "forge_main::fs::read",
            stack_trace.clone(),
        );

        if let EventKind::ErrorOccurred(details) = error2 {
            assert_eq!(details.error_type, "FileError");
            assert_eq!(details.message, "File not found");
            assert_eq!(details.context, "forge_main::fs::read");
            assert_eq!(details.stack_trace, Some(stack_trace));
        } else {
            panic!("Expected ErrorOccurred variant");
        }
    }
}
