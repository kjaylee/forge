use std::fmt::Display;

use schemars::schema::RootSchema;

use crate::ToolDefinition;

#[derive(Debug)]
pub struct ToolUsagePrompt {
    tool_name: String,
    input_schema: RootSchema,
    description: String,
}

impl Display for ToolUsagePrompt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.tool_name)?;
        f.write_str("\n")?;
        f.write_str(&self.description.replace("\n", " "))?;
        f.write_str("\nJson Schema:\n")?;
        f.write_str(&serde_json::to_string_pretty(&self.input_schema).unwrap())?;
        Ok(())
    }
}

impl From<ToolDefinition> for ToolUsagePrompt {
    fn from(value: ToolDefinition) -> Self {
        Self {
            tool_name: value.name.clone().into_string(),
            input_schema: value.input_schema,
            description: value.description.to_string(),
        }
    }
}
