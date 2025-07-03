use derive_more::From;
use forge_domain::ToolName;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Invalid tool call arguments: {0}")]
    CallArgument(ToolCallParameterError),

    #[error("Tool {0} not found")]
    NotFound(ToolName),

    #[error("Tool '{tool_name}' timed out after {timeout} minutes")]
    CallTimeout { tool_name: ToolName, timeout: u64 },

    #[error(
        "Tool '{name}' is not available. Please try again with one of these tools: [{supported_tools}]"
    )]
    NotAllowed {
        name: ToolName,
        supported_tools: String,
    },

    #[error("Empty tool response")]
    EmptyToolResponse,
}

#[derive(Debug, From)]
pub struct ToolCallParameterError(eserde::DeserializationErrors);

impl std::fmt::Display for ToolCallParameterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Invalid parameters:")?;
        for error in self.0.iter() {
            writeln!(f, "- {error}")?;
        }
        Ok(())
    }
}
