use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Sends a formatted markdown message to the user's terminal display.
/// This tool allows the agent to communicate information to the user with
/// proper text formatting. Use this when you need to display structured content
/// such as headers, lists, tables, code blocks, or text with emphasis
/// (bold/italic). The content parameter must contain valid markdown syntax. The
/// tool will render this content in the terminal with appropriate formatting
/// using the termimad library. Do NOT use this tool for collecting user input
/// or for messages that don't benefit from formatting. Returns a simple
/// confirmation string but does not capture user responses.
#[derive(Clone, Default, ToolDescription)]
pub struct ShowUser;

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ShowUserInput {
    /// The markdown content to display to the user. Should contain valid
    /// markdown syntax such as headers (#), lists (-, *), emphasis
    /// (**bold**, *italic*), code blocks, and other markdown formatting
    /// elements.
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
    async fn call(
        &self,
        input: Self::Input,
        _conversation: &forge_domain::Conversation,
    ) -> anyhow::Result<String> {
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
        use std::path::PathBuf;

        use forge_domain::{Conversation, ConversationId, Workflow};

        let show_user = ShowUser;
        let input = ShowUserInput {
            content: "# Test Heading\nThis is a test with **bold** and *italic* text.".to_string(),
        };

        // Create a mock conversation for testing
        let conversation = Conversation::new(
            ConversationId::generate(),
            Workflow::default(),
            PathBuf::from("/test"),
        );

        // The function should execute without error and return a success message
        let result = show_user.call(input, &conversation).await;
        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            "Markdown content displayed to user".to_string()
        );
    }
}
