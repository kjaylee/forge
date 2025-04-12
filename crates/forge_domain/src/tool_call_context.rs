use serde::{Deserialize, Serialize};

/// Provides additional context for tool calls.
/// Currently empty but structured to allow for future extension.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ToolCallContext {
    // Note: Currently empty, but fields can be added here in the future as needed
}

impl ToolCallContext {
    /// Create a new empty context
    pub fn new() -> Self {
        Self::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_context() {
        let context = ToolCallContext::new();
        assert!(matches!(context, ToolCallContext {}));
    }

    #[test]
    fn test_for_tests() {
        let context = ToolCallContext::default();
        assert!(matches!(context, ToolCallContext {}));
    }
}
