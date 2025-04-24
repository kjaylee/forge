use std::fmt::Display;

use crate::ToolDefinition;

pub struct ToolUsagePrompt<'a> {
    tools: &'a Vec<ToolDefinition>,
}

impl<'a> From<&'a Vec<ToolDefinition>> for ToolUsagePrompt<'a> {
    fn from(value: &'a Vec<ToolDefinition>) -> Self {
        Self { tools: value }
    }
}

impl Display for ToolUsagePrompt<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, tool) in self.tools.iter().enumerate() {
            writeln!(f, "{}. {}:", i + 1, tool.name.as_str())?;
            writeln!(f, "{}", &tool.description)?;

            writeln!(f, "\n\nUsage:")?;
            writeln!(f, "<tool_call>")?;
            writeln!(f, "<{}>", tool.name.as_str())?;

            let parameters = tool
                .input_schema
                .schema
                .object
                .clone()
                .into_iter()
                .flat_map(|object| object.properties.into_iter().map(|(name, _)| name));

            for parameter in parameters {
                writeln!(f, "<{parameter}>...</{parameter}>")?;
            }

            writeln!(f, "</{}>", tool.name.as_str())?;
            writeln!(f, "{}", "</tool_call>")?;
        }

        Ok(())
    }
}
