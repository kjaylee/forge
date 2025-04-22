use std::sync::Arc;

use anyhow::Result;
use forge_domain::{ExecutableTool, NamedTool, ToolCallContext, ToolDescription};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::infra::InquireService;
use crate::Infrastructure;

/// Ask the user a question to gather additional information needed to complete
/// the task. This tool should be used when you encounter ambiguities, need
/// clarification, or require more details to proceed effectively. It allows for
/// interactive problem-solving by enabling direct communication with the user.
/// Use this tool judiciously to maintain a balance between gathering necessary
/// information and avoiding excessive back-and-forth
#[derive(Debug, ToolDescription)]
pub struct Followup<F> {
    infra: Arc<F>,
}

impl<F> Followup<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

impl<F: Infrastructure> NamedTool for Followup<F> {
    fn tool_name() -> forge_domain::ToolName {
        forge_domain::ToolName::new("tool_forge_followup")
    }
}

/// Input for the select tool
#[derive(Deserialize, JsonSchema)]
pub struct SelectInput {
    /// Message to display as prompt to the user
    pub message: String,

    /// List of options to choose from
    pub options: Vec<String>,

    /// If true, allows selecting multiple options; if false, only one option
    /// can be selected
    #[schemars(default)]
    pub multiple: bool,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for Followup<F> {
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
    use forge_domain::ToolName;
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_tool_name() {
        let expected = ToolName::new("tool_forge_select");
        let actual = <Followup<crate::tools::registry::tests::Stub> as NamedTool>::tool_name();
        assert_eq!(actual, expected);
    }

    // Note: We can't easily test the actual select functionality without
    // mocking user input
}
