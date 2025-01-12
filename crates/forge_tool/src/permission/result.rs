use std::fmt::{self, Display};
use std::path::{Path, PathBuf};
use forge_domain::{Permission};

/// Represents a permission operation result with formatting options.
#[derive(Debug, Clone)]
pub struct PermissionResultDisplay {
    pub allowed: bool,
    pub permission: Permission,
    pub path: PathBuf,
    pub context: Option<String>,
}

impl PermissionResultDisplay {
    /// Create a new permission result display
    pub fn new(allowed: bool, permission: Permission, path: impl AsRef<Path>, context: Option<String>) -> Self {
        Self {
            allowed,
            permission,
            path: path.as_ref().to_path_buf(),
            context,
        }
    }

    /// Create a simple result without context
    pub fn simple(allowed: bool, permission: Permission, path: impl AsRef<Path>) -> Self {
        Self::new(allowed, permission, path, None)
    }

    /// Format result for human readers
    fn format_human(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Permission {} for {} access to {}",
            if self.allowed { "granted" } else { "denied" },
            match self.permission {
                Permission::Read => "read",
                Permission::Write => "write",
                Permission::Execute => "execute",
                Permission::Deny => "any",
            },
            self.path.display(),
        )?;

        if let Some(context) = &self.context {
            write!(f, "\nContext: {}", context)?;
        }

        Ok(())
    }

    /// Format result for LLM consumption
    fn format_llm(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "<permission_result>")?;
        writeln!(f, "  <state>{}</state>", if self.allowed { "granted" } else { "denied" })?;
        writeln!(f, "  <permission>{:?}</permission>", self.permission)?;
        writeln!(f, "  <path>{}</path>", self.path.display())?;
        
        if let Some(context) = &self.context {
            writeln!(f, "  <context>{}</context>", context)?;
        }

        write!(f, "</permission_result>")
    }
}

impl Display for PermissionResultDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            self.format_llm(f)
        } else {
            self.format_human(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;

    #[test]
    fn test_simple_result_display() {
        let result = PermissionResultDisplay::simple(
            true,
            Permission::Read,
            "/test/path",
        );

        let display = result.to_string();
        assert!(display.contains("Permission granted"));
        assert!(display.contains("read access"));
        assert!(display.contains("/test/path"));
    }

    #[test]
    fn test_result_with_context() {
        let result = PermissionResultDisplay::new(
            false,
            Permission::Write,
            "/test/path",
            Some("Security policy violation".to_string()),
        );

        let display = result.to_string();
        assert!(display.contains("Permission denied"));
        assert!(display.contains("write access"));
        assert!(display.contains("Security policy violation"));
    }

    #[test]
    fn test_deny_permission() {
        let result = PermissionResultDisplay::simple(
            false,
            Permission::Deny,
            "/test/path",
        );

        let display = result.to_string();
        assert!(display.contains("Permission denied"));
        assert!(display.contains("any access"));
        assert!(display.contains("/test/path"));
    }

    #[test]
    fn test_execute_permission() {
        let result = PermissionResultDisplay::simple(
            true,
            Permission::Execute,
            "/test/script.sh",
        );

        let display = result.to_string();
        assert!(display.contains("Permission granted"));
        assert!(display.contains("execute access"));
        assert!(display.contains("/test/script.sh"));
    }

    #[test]
    fn test_llm_format() {
        let result = PermissionResultDisplay::new(
            true,
            Permission::Execute,
            "/test/path",
            Some("User approved".to_string()),
        );

        let display = format!("{:#}", result);
        assert_snapshot!(display);
    }

    #[test]
    fn test_llm_format_denied() {
        let result = PermissionResultDisplay::new(
            false,
            Permission::Write,
            "/test/path",
            Some("In deny list".to_string()),
        );

        let display = format!("{:#}", result);
        assert_snapshot!(display);
    }
}
