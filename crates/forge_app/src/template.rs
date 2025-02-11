//! Template loading utilities for Code-Forge
//!
//! This module provides macros for loading templates at compile time.
//! Templates are stored in the `templates` directory at the workspace root.

/// Load a template file at compile time
///
/// # Examples
///
/// ```rust
/// // Load a role template
/// let role_template = template!("roles/title-generator");
///
/// // Load a partial template
/// let partial = template!("partials/agent-system");
/// ```
#[macro_export]
macro_rules! template {
    ($path:expr) => {
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../templates/",
            $path,
            ".mustache"
        ))
    };
}

/// Load a role template at compile time
///
/// This is a convenience wrapper around `template!` that prepends "roles/"
///
/// # Examples
///
/// ```rust
/// let template = role_template!("title-generator");
/// ```
#[macro_export]
macro_rules! role_template {
    ($name:expr) => {
        template!(concat!("roles/", $name))
    };
}

/// Load a partial template at compile time
///
/// This is a convenience wrapper around `template!` that prepends "partials/"
///
/// # Examples
///
/// ```rust
/// let template = partial_template!("agent-system");
/// ```
#[macro_export]
macro_rules! partial_template {
    ($name:expr) => {
        template!(concat!("partials/", $name))
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_load_templates() {
        // Test loading a role template
        let title_template = template!("roles/title-generator");
        assert!(title_template.contains("Code-Forge's Title Generation Expert"));

        // Test loading another role template
        let engineer_template = template!("roles/software-engineer");
        assert!(engineer_template.contains("Code-Forge"));

        // Test using role_template! macro
        let title = role_template!("title-generator");
        assert!(title.contains("Code-Forge's Title Generation Expert"));

        // Test using partial_template! macro
        let tools = partial_template!("tool-usage-examples");
        assert!(tools.contains("tool_forge_fs_read"));
    }
}
