use std::fmt::Write;
use std::time::Duration;

use async_trait::async_trait;
use tokio::time::timeout;
use forge_domain::{
    PermissionInteraction,
    PermissionRequest,
    PermissionResult,
    PermissionState,
    PermissionError,
};

use crate::ask;

/// CLI-based permission handler that interacts with users
/// through command line interface.
#[derive(Debug, Clone)]
pub struct CliPermissionHandler {
    /// Default timeout for requests
    timeout: Duration,
}

impl Default for CliPermissionHandler {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
        }
    }
}

impl CliPermissionHandler {
    /// Create a new CLI permission handler with custom timeout
    #[cfg(test)]
    pub fn new(timeout: Duration) -> Self {
        Self { timeout }
    }

    /// Convert user input into permission state
    fn parse_response(input: &str) -> PermissionResult<PermissionState> {
        let input = input.trim().to_uppercase();
        if input.starts_with("[R]") {
            Ok(PermissionState::Reject)
        } else if input.starts_with("[A]") {
            Ok(PermissionState::Allow)
        } else if input.starts_with("[S]") {
            Ok(PermissionState::AllowSession)
        } else if input.starts_with("[F]") {
            Ok(PermissionState::AllowForever)
        } else {
            // Also accept single letter responses
            match input.as_str() {
                "R" => Ok(PermissionState::Reject),
                "A" => Ok(PermissionState::Allow),
                "S" => Ok(PermissionState::AllowSession),
                "F" => Ok(PermissionState::AllowForever),
                _ => Err(PermissionError::InvalidResponse),
            }
        }
    }
}

#[async_trait]
impl PermissionInteraction for CliPermissionHandler {
    fn format_request(&self, request: &PermissionRequest) -> String {
        let mut output = String::new();
        
        // Title
        writeln!(output, "Permission Required").unwrap();
        writeln!(output).unwrap();
        
        // Request details
        writeln!(output, "Tool:      {}", request.tool_name()).unwrap();
        writeln!(output, "Action:    {}", request.operation()).unwrap();
        writeln!(output, "Path:      {}", request.path().display()).unwrap();
        
        if let Some(context) = request.context() {
            writeln!(output, "Context:   {}", context).unwrap();
        }
        
        writeln!(output).unwrap();
        
        output
    }

    async fn request_permission_timeout(
        &self,
        request: &PermissionRequest,
        timeout_duration: Duration,
    ) -> PermissionResult<PermissionState> {
        let message = self.format_request(request);
        let options = vec![
            "[R] Reject (deny this time)",
            "[A] Allow (allow this time)",
            "[S] Allow for Session (until program exit)",
            "[F] Allow Forever (save to config)",
        ];

        match timeout(
            timeout_duration,
            ask::select(&message, &options)
        ).await {
            Ok(Ok(input)) => Self::parse_response(&input),
            Ok(Err(e)) => Err(PermissionError::InteractionFailed(e.to_string())),
            Err(_) => Err(PermissionError::InteractionTimeout),
        }
    }

    async fn request_permission(
        &self,
        request: &PermissionRequest,
    ) -> PermissionResult<PermissionState> {
        self.request_permission_timeout(request, self.timeout).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn create_test_request() -> PermissionRequest {
        PermissionRequest::new(
            PathBuf::from("/test/path"),
            "test_tool".to_string(),
            "read".to_string(),
        ).with_context("Test context".to_string())
    }

    #[test]
    fn test_format_request() {
        let handler = CliPermissionHandler::default();
        let request = create_test_request();

        let formatted = handler.format_request(&request);
        
        // Basic validation
        assert!(formatted.contains("Permission Required"));
        assert!(formatted.contains("test_tool"));
        assert!(formatted.contains("/test/path"));
    }

    #[test]
    fn test_format_request_with_context() {
        let handler = CliPermissionHandler::default();
        let request = create_test_request();

        let formatted = handler.format_request(&request);
        
        assert!(formatted.contains("Test context"));
    }

    #[test]
    fn test_parse_response_valid() {
        assert!(matches!(
            CliPermissionHandler::parse_response("R").unwrap(),
            PermissionState::Reject
        ));
        assert!(matches!(
            CliPermissionHandler::parse_response("A").unwrap(),
            PermissionState::Allow
        ));
        assert!(matches!(
            CliPermissionHandler::parse_response("S").unwrap(),
            PermissionState::AllowSession
        ));
        assert!(matches!(
            CliPermissionHandler::parse_response("F").unwrap(),
            PermissionState::AllowForever
        ));
    }

    #[test]
    fn test_parse_response_case_insensitive() {
        assert!(matches!(
            CliPermissionHandler::parse_response("r").unwrap(),
            PermissionState::Reject
        ));
        assert!(matches!(
            CliPermissionHandler::parse_response("a").unwrap(),
            PermissionState::Allow
        ));
    }

    #[test]
    fn test_parse_response_invalid() {
        assert!(matches!(
            CliPermissionHandler::parse_response("X"),
            Err(PermissionError::InvalidResponse)
        ));
        assert!(matches!(
            CliPermissionHandler::parse_response(""),
            Err(PermissionError::InvalidResponse)
        ));
    }

    #[tokio::test]
    async fn test_request_permission_timeout() {
        let handler = CliPermissionHandler::new(Duration::from_millis(1));
        let request = create_test_request();

        // Should timeout almost immediately
        let result = handler.request_permission(&request).await;
        assert!(matches!(result, Err(PermissionError::InteractionTimeout)));
    }
}
