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
            writeln!(f, "<forge_tool_call>")?;
            writeln!(f, "<{}>", tool.name.as_str())?;

            let parameters = tool
                .input_schema
                .schema
                .object
                .clone()
                .into_iter()
                .flat_map(|object| object.properties.into_keys());

            for parameter in parameters {
                writeln!(f, "<{parameter}>...</{parameter}>")?;
            }

            writeln!(f, "</{}>", tool.name.as_str())?;
            writeln!(f, "</forge_tool_call>\n\n")?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use schemars::schema::{
        InstanceType, ObjectValidation, RootSchema, Schema, SchemaObject, SingleOrVec,
    };
    use std::collections::BTreeMap;

    use crate::{ToolDefinition, ToolName};

    use super::*;

    /// Create a test tool definition with specified parameters
    fn create_tool_definition(
        name: &str,
        description: &str,
        parameters: &[&str],
    ) -> ToolDefinition {
        // Create a schema object with the specified parameters
        let mut properties = BTreeMap::new();
        for param in parameters {
            let schema_obj = SchemaObject {
                instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::String))),
                ..Default::default()
            };
            properties.insert(param.to_string(), Schema::Object(schema_obj));
        }

        let obj_validation = ObjectValidation {
            properties,
            ..Default::default()
        };

        let schema_obj = SchemaObject {
            instance_type: Some(SingleOrVec::Single(Box::new(InstanceType::Object))),
            object: Some(Box::new(obj_validation)),
            ..Default::default()
        };

        let root_schema = RootSchema {
            schema: schema_obj,
            ..Default::default()
        };

        ToolDefinition {
            name: ToolName::new(name),
            description: description.to_string(),
            input_schema: root_schema,
            output_schema: None,
        }
    }

    #[test]
    fn test_tool_usage_prompt_to_string() {
        // Create test tools with different parameters
        let tool1 = create_tool_definition(
            "forge_tool_test",
            "Test tool description for testing purposes.",
            &["param1", "param2"],
        );

        let tool2 = create_tool_definition(
            "forge_tool_another",
            "Another tool description with different parameters.",
            &["path", "content", "option"],
        );

        // Create a vector of tool definitions
        let tools = vec![tool1, tool2];

        // Create the ToolUsagePrompt
        let prompt = ToolUsagePrompt::from(&tools);

        // Convert to string
        let actual = prompt.to_string();

        // Define expected output
        let expected = r#"1. forge_tool_test:
Test tool description for testing purposes.


Usage:
<forge_tool_call>
<forge_tool_test>
<param1>...</param1>
<param2>...</param2>
</forge_tool_test>
</forge_tool_call>


2. forge_tool_another:
Another tool description with different parameters.


Usage:
<forge_tool_call>
<forge_tool_another>
<content>...</content>
<option>...</option>
<path>...</path>
</forge_tool_another>
</forge_tool_call>


"#;

        // Assert the output matches expected
        assert_eq!(actual, expected);
    }
}
