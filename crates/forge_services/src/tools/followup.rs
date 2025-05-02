use std::sync::Arc;

use anyhow::Result;
use forge_domain::{ExecutableTool, NamedTool, ToolCallContext, ToolDescription};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::infra::InquireService;
use crate::Infrastructure;

/// Use this tool when you encounter ambiguities, need clarification, or require
/// more details to proceed effectively. Use this tool judiciously to maintain a
/// balance between gathering necessary information and avoiding excessive
/// back-and-forth.
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
    /// Question to ask the user
    pub question: String,

    /// First option to choose from
    pub option1: Option<String>,

    /// Second option to choose from
    pub option2: Option<String>,

    /// Third option to choose from
    pub option3: Option<String>,

    /// Fourth option to choose from
    pub option4: Option<String>,

    /// Fifth option to choose from
    pub option5: Option<String>,

    /// If true, allows selecting multiple options; if false (default), only one option
    /// can be selected
    #[schemars(default)]
    pub multiple: Option<bool>,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for Followup<F> {
    type Input = SelectInput;

    async fn call(&self, _: ToolCallContext, input: Self::Input) -> Result<String> {
        let options = vec![
            input.option1,
            input.option2,
            input.option3,
            input.option4,
            input.option5,
        ]
        .into_iter()
        .filter(|opt| opt.is_some())
        .flatten()
        .collect::<Vec<_>>();

        // Options are empty means question requires descriptive answer.
        let result = if options.is_empty() {
            self.infra
                .inquire_service()
                .prompt_question(&input.question)
                .await?
        } else {
            // Use the select service to get user selection
            if input.multiple.unwrap_or_default() {
                let selected = self
                    .infra
                    .inquire_service()
                    .select_many(&input.question, options)
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
                    .select_one(&input.question, options)
                    .await?;
                format!("User selected: {selected}")
            }
        };

        Ok(result)
    }
}
