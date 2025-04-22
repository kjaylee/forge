use anyhow::Result;
use forge_domain::{ExecutableTool, NamedTool, ToolCallContext, ToolDescription};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

/// Marks a task as completed with the provided summary message. When this tool
/// is called, the system will set the completion flag to indicate that the task
/// has been successfully completed. Use this tool when you want to signal that
/// a workflow or task sequence has reached its intended conclusion.
#[derive(Debug, Default, ToolDescription)]
pub struct Completion;

impl NamedTool for Completion {
    fn tool_name() -> forge_domain::ToolName {
        forge_domain::ToolName::new("tool_forge_attempt_completion")
    }
}

#[derive(Deserialize, JsonSchema)]
pub struct AttemptCompletionInput {
    /// Summary message describing the completed task
    message: String,
}

#[async_trait::async_trait]
impl ExecutableTool for Completion {
    type Input = AttemptCompletionInput;

    async fn call(&self, context: ToolCallContext, input: Self::Input) -> Result<String> {
        let result_message = format!("Task completed: {}", input.message);

        // Log the completion event
        context.send_text(result_message.clone()).await?;

        // Return success with the message and completion flag set to true
        Ok(result_message)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[tokio::test]
    async fn test_attempt_completion() {
        // Create fixture
        let tool = Completion;
        let input =
            AttemptCompletionInput { message: "All required features implemented".to_string() };

        // Execute the fixture
        let actual = tool.call(ToolCallContext::default(), input).await.unwrap();

        // Define expected result
        let expected = "Task completed: All required features implemented";

        // Assert that the actual result matches the expected result
        assert_eq!(actual, expected);
    }
}
