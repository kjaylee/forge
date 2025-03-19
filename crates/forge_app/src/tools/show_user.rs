use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Renders markdown content to the terminal for user display.
/// This tool takes plain text with markdown formatting and
/// renders it directly to the terminal with proper formatting.
#[derive(Clone, Default, ToolDescription)]
pub struct ShowUser;

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ShowUserInput {
    /// The markdown content to render
    pub content: String,
}

impl NamedTool for ShowUser {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_display_show_user")
    }
}

#[async_trait::async_trait]
impl ExecutableTool for ShowUser {
    type Input = ShowUserInput;
    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        // Use termimad to display the markdown to the terminal

        let skin = termimad::get_default_skin();
        let content = skin.term_text(&input.content);
        println!("{}", content);

        // Return a simple success message
        Ok("Markdown content displayed to user".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_show_user() {
        let show_user = ShowUser;
        let input = ShowUserInput {
            content: "# Test Heading\nThis is a test with **bold** and *italic* text.".to_string(),
        };

        // The function should execute without error and return a success message
        let result = show_user.call(input).await;
        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            "Markdown content displayed to user".to_string()
        );
    }
}
