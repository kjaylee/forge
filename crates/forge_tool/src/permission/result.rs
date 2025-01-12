use std::fmt::{self, Display};
use forge_domain::{PermissionRequest, PermissionState};

/// Represents a permission request result with human and LLM-friendly formatting.
/// This type provides context-rich information about permission decisions.
#[derive(Debug, Clone)]
pub struct PermissionResultDisplay {
    /// The state of the permission (allow/deny/etc)
    pub state: PermissionState,
    /// The original request that led to this result
    pub request: PermissionRequest,
    /// Optional additional context about the decision
    pub context: Option<String>,
}

impl PermissionResultDisplay {
    /// Create a new permission result display
    pub fn new(
        state: PermissionState,
        request: PermissionRequest,
        context: Option<String>,
    ) -> Self {
        Self {
            state,
            request,
            context,
        }
    }

    /// Create a new permission result without additional context
    pub fn simple(
        state: PermissionState,
        request: PermissionRequest,
    ) -> Self {
        Self::new(state, request, None)
    }

    /// Get a human-readable description of the permission scope
    fn scope_description(&self) -> &'static str {
        match self.state {
            PermissionState::Reject => "denied",
            PermissionState::Allow => "granted (one-time)",
            PermissionState::AllowSession => "granted (for this session)",
            PermissionState::AllowForever => "granted (permanently)",
        }
    }

    /// Format the result for human readers
    fn format_human(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Permission {} for {} to {} {}",
            self.scope_description(),
            self.request.tool_name(),
            self.request.operation(),
            self.request.path().display(),
        )?;

        // Add context if available
        if let Some(context) = &self.context {
            write!(f, "\nContext: {}", context)?;
        }

        // Add request context if available
        if let Some(req_context) = self.request.context() {
            write!(f, "\nRequest Context: {}", req_context)?;
        }

        Ok(())
    }

    /// Format the result for LLM consumption
    fn format_llm(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "<permission_result>")?;
        writeln!(f, "  <state>{}</state>", self.scope_description())?;
        writeln!(f, "  <tool>{}</tool>", self.request.tool_name())?;
        writeln!(f, "  <operation>{}</operation>", self.request.operation())?;
        writeln!(f, "  <path>{}</path>", self.request.path().display())?;

        if let Some(context) = &self.context {
            writeln!(f, "  <context>{}</context>", context)?;
        }

        if let Some(req_context) = self.request.context() {
            writeln!(f, "  <request_context>{}</request_context>", req_context)?;
        }

        write!(f, "</permission_result>")
    }
}

impl Display for PermissionResultDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            // Use alternate format (#) for LLM output
            self.format_llm(f)
        } else {
            // Use regular format for human output
            self.format_human(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use insta::assert_snapshot;

    fn create_test_request() -> PermissionRequest {
        PermissionRequest::new(
            PathBuf::from("/test/path"),
            "test_tool",
            "read",
        )
    }

    fn create_test_request_with_context() -> PermissionRequest {
        PermissionRequest::new(
            PathBuf::from("/test/path"),
            "test_tool",
            "write",
        ).with_context("Important operation")
    }

    #[test]
    fn test_simple_result_display() {
        let request = create_test_request();
        let result = PermissionResultDisplay::simple(
            PermissionState::Allow,
            request,
        );

        assert_snapshot!(result.to_string());
    }

    #[test]
    fn test_result_with_context() {
        let request = create_test_request();
        let result = PermissionResultDisplay::new(
            PermissionState::Reject,
            request,
            Some("Security policy violation".to_string()),
        );

        let display = result.to_string();
        assert!(display.contains("Permission denied"));
        assert!(display.contains("Security policy violation"));
    }

    #[test]
    fn test_result_with_request_context() {
        let request = create_test_request_with_context();
        let result = PermissionResultDisplay::simple(
            PermissionState::AllowSession,
            request,
        );

        let display = result.to_string();
        assert!(display.contains("granted (for this session)"));
        assert!(display.contains("Important operation"));
    }

    #[test]
    fn test_result_with_all_contexts() {
        let request = create_test_request_with_context();
        let result = PermissionResultDisplay::new(
            PermissionState::AllowForever,
            request,
            Some("User approved".to_string()),
        );

        let display = result.to_string();
        assert!(display.contains("granted (permanently)"));
        assert!(display.contains("User approved"));
        assert!(display.contains("Important operation"));
    }

    #[test]
    fn test_llm_format() {
        let request = create_test_request_with_context();
        let result = PermissionResultDisplay::new(
            PermissionState::Allow,
            request,
            Some("User approved".to_string()),
        );

        let display = format!("{:#}", result);
        assert_snapshot!(display);
    }

    #[test]
    fn test_llm_format_minimal() {
        let request = create_test_request();
        let result = PermissionResultDisplay::simple(
            PermissionState::Reject,
            request,
        );

        let display = format!("{:#}", result);
        assert_snapshot!(display);
    }
}