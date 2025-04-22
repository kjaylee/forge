use anyhow::Result;
use forge_domain::{ExecutableTool, NamedTool, ToolCallContext, ToolDescription};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;
use std::sync::Arc;

use crate::infra::InquireService;
use crate::Infrastructure;

/// Provides interactive selection functionality for a list of options. The tool
/// supports both single-option selection and multiple-option selection modes.
/// Use this tool when you need to prompt the user to make one or more choices
/// from a predefined list of options.
#[derive(Debug, ToolDescription)]
pub struct Feedback<F> {
    infra: Arc<F>,
}

impl<F> Feedback<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F: Infrastructure> NamedTool for Feedback<F> {
    fn tool_name() -> forge_domain::ToolName {
        forge_domain::ToolName::new("tool_forge_user_feedback")
    }
}

/// Input for the select tool
#[derive(Deserialize, JsonSchema)]
pub struct SelectInput {
    /// Message to display as prompt to the user
    pub message: String,

    /// List of options to choose from
    pub options: Vec<String>,

    /// If true, allows selecting multiple options; if false, only one option can be selected
    #[schemars(default)]
    pub multiple: bool,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for Feedback<F> {
    type Input = SelectInput;

    async fn call(&self, _: ToolCallContext, input: Self::Input) -> Result<String> {
        // Use the select service to get user selection
        let result = if input.multiple {
            let selected = self
                .infra
                .inquire_service()
                .select_many(&input.message, input.options)
                .await?;
            format!(
                "User selected {} option(s): {}",
                selected.len(),
                selected.join(", ")
            )
        } else {
            let selected = self
                .infra
                .inquire_service()
                .select_one(&input.message, input.options)
                .await?;
            format!("User selected: {}", selected)
        };

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use forge_domain::ToolName;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_tool_name() {
        let expected = ToolName::new("tool_forge_select");
        let actual = <Feedback<crate::tools::registry::tests::Stub> as NamedTool>::tool_name();
        assert_eq!(actual, expected);
    }

    // Note: We can't easily test the actual select functionality without mocking user input
}
