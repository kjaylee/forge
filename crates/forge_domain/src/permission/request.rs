use std::path::{Path, PathBuf};

/// A request for permission to perform an operation
#[derive(Debug, Clone)]
pub struct PermissionRequest {
    /// Path being accessed
    path: PathBuf,
    /// Tool requesting access
    tool_name: String,
    /// Operation being performed (read, write, etc)
    operation: String,
    /// Additional context for the user
    context: Option<String>,
}

impl PermissionRequest {
    /// Create a new permission request
    pub fn new(
        path: impl AsRef<Path>,
        tool_name: impl Into<String>,
        operation: impl Into<String>,
    ) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
            tool_name: tool_name.into(),
            operation: operation.into(),
            context: None,
        }
    }

    /// Add context to the request
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Get the path being accessed
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Get the tool name
    pub fn tool_name(&self) -> &str {
        &self.tool_name
    }

    /// Get the operation being performed
    pub fn operation(&self) -> &str {
        &self.operation
    }

    /// Get the context if any
    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }
}

impl From<&PermissionRequest> for String {
    fn from(request: &PermissionRequest) -> Self {
        format!(
            "{} requesting {} access to {}{}",
            request.tool_name,
            request.operation,
            request.path.display(),
            request.context
                .as_ref()
                .map(|ctx| format!(" ({})", ctx))
                .unwrap_or_default()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permission_request_creation() {
        let request = PermissionRequest::new(
            "/test/path",
            "test_tool",
            "read"
        );

        assert_eq!(request.path().to_str().unwrap(), "/test/path");
        assert_eq!(request.tool_name(), "test_tool");
        assert_eq!(request.operation(), "read");
        assert_eq!(request.context(), None);
    }

    #[test]
    fn test_permission_request_with_context() {
        let request = PermissionRequest::new(
            "/test/path",
            "test_tool",
            "write"
        ).with_context("test context");

        assert_eq!(request.context(), Some("test context"));
    }

    #[test]
    fn test_permission_request_to_string() {
        let request = PermissionRequest::new(
            "/test/path",
            "test_tool",
            "read"
        );
        let string: String = (&request).into();
        assert_eq!(
            string,
            "test_tool requesting read access to /test/path"
        );

        let request_with_context = request.with_context("important operation");
        let string: String = (&request_with_context).into();
        assert_eq!(
            string,
            "test_tool requesting read access to /test/path (important operation)"
        );
    }

    #[test]
    fn test_permission_request_cloning() {
        let original = PermissionRequest::new(
            "/test/path",
            "test_tool",
            "read"
        ).with_context("test context");

        let cloned = original.clone();

        assert_eq!(original.path(), cloned.path());
        assert_eq!(original.tool_name(), cloned.tool_name());
        assert_eq!(original.operation(), cloned.operation());
        assert_eq!(original.context(), cloned.context());
    }
}