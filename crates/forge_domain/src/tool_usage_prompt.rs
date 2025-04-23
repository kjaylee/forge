use std::collections::BTreeSet;
use std::fmt::Display;

use schemars::schema::RootSchema;

use crate::ToolDefinition;

#[derive(Debug)]
pub struct ToolUsagePrompt {
    pub tool_name: String,
    pub input_parameters: Vec<UsageParameterPrompt>,
    pub description: String,
}

impl Display for ToolUsagePrompt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.tool_name)?;
        f.write_str("\n")?;
        f.write_str(&self.description)?;

        f.write_str("\n\nUsage:\n")?;
        f.write_str("<tool_call>\n")?;
        f.write_str("<")?;
        f.write_str(&self.tool_name)?;
        f.write_str(">")?;

        for parameter in self.input_parameters.iter() {
            f.write_str("\n")?;
            parameter.fmt(f)?;
        }

        f.write_str("\n")?;
        f.write_str("</")?;
        f.write_str(&self.tool_name)?;
        f.write_str(">\n")?;
        f.write_str("</tool_call>\n")?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct UsageParameterPrompt {
    pub parameter_name: String,
    pub parameter_type: String,
}

impl Display for UsageParameterPrompt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<")?;
        f.write_str(&self.parameter_name)?;
        f.write_str(">")?;
        f.write_str(&self.parameter_type)?;
        f.write_str("</")?;
        f.write_str(&self.parameter_name)?;
        f.write_str(">")?;

        Ok(())
    }
}

impl From<ToolDefinition> for ToolUsagePrompt {
    fn from(value: ToolDefinition) -> Self {
        let input_parameters = value
            .input_schema
            .schema
            .object
            .clone()
            .map(|object| {
                object
                    .properties
                    .keys()
                    .map(|name| UsageParameterPrompt {
                        parameter_name: name.to_string(),
                        parameter_type: "...".to_string(),
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();

        let input: RootSchema = value.input_schema.clone();
        let mut description = value.description.clone();

        description.push_str("\n\nParameters:");

        let required = input
            .schema
            .clone()
            .object
            .iter()
            .flat_map(|object| object.required.clone().into_iter())
            .collect::<BTreeSet<_>>();

        for (name, desc) in input
            .schema
            .object
            .clone()
            .into_iter()
            .flat_map(|object| object.properties.into_iter())
            .flat_map(|(name, props)| {
                props
                    .into_object()
                    .metadata
                    .into_iter()
                    .map(move |meta| (name.clone(), meta))
            })
            .flat_map(|(name, meta)| {
                meta.description
                    .into_iter()
                    .map(move |desc| (name.clone(), desc))
            })
        {
            description.push_str("\n- ");
            description.push_str(&name);

            if required.contains(&name) {
                description.push_str(" (required)");
            }

            description.push_str(": ");
            description.push_str(&desc);
        }

        Self {
            tool_name: value.name.clone().into_string(),
            input_parameters,
            description: value.description.to_string(),
        }
    }
}
