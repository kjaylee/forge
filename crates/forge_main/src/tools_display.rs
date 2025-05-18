use colored::Colorize;
use forge_api::ToolDefinition;
use forge_display::markdown::MarkdownFormat;

/// Formats the list of tools for display in the shell UI, using a simple and
/// clean text-based format:
/// - Tool name as a blue bold heading
/// - Description as a paragraph
/// - Input schema as a simple, clean table
/// - Required fields marked with emoji
/// - Line separator after each tool
pub fn format_tools(tools: &[ToolDefinition]) -> String {
    let mut output = String::new();

    for (i, tool) in tools.iter().enumerate() {
        // Format tool name as blue bold
        let name = tool.name.to_string().blue().bold();
        let description = &tool.description;

        // Add tool name and description
        output.push_str(&format!("## {name}\n\n{description}"));

        // Parse input schema to extract properties
        if let Ok(schema_value) = serde_json::to_value(&tool.input_schema) {
            if let Some(properties) = schema_value.get("properties").and_then(|p| p.as_object()) {
                if !properties.is_empty() {
                    // Get required properties as strings
                    let required_props = schema_value
                        .get("required")
                        .and_then(|r| r.as_array())
                        .map_or_else(Vec::new, |arr| {
                            arr.iter().filter_map(|v| v.as_str()).collect::<Vec<_>>()
                        });

                    // Add table header
                    output.push_str("\n\n**Input Schema**\n\n");

                    // Add a line for each property
                    for (prop_name, prop_value) in properties {
                        // Extract the type information
                        let mut prop_type = extract_type_info(prop_value).trim().to_string();

                        if required_props.contains(&prop_name.trim()) {
                            prop_type = format!("{prop_type}\\*");
                        }

                        let desc = prop_value
                            .get("description")
                            .and_then(|d| d.as_str())
                            .unwrap_or("");

                        // Format as: property_name: (type) description
                        output.push_str(&format!(
                            "{}: {}",
                            prop_name.bold(),
                            format!("({})", prop_type.cyan()).bold()
                        ));
                        if !desc.is_empty() {
                            output.push_str(&format!(" - {desc}"));
                        }
                        output.push('\n');
                    }
                } else {
                    output.push_str("\n\n**Input Schema:** No input properties defined.");
                }
            } else {
                output.push_str("\n\n**Input Schema:** No input properties defined.");
            }
        } else {
            output.push_str("\n\n**Input Schema:** No input schema defined.");
        }

        // Add separator after each tool except the last one
        if i < tools.len() - 1 {
            output.push_str("\n---\n\n");
        }
    }

    // Use the markdown formatter to render the final output
    let formatter = MarkdownFormat::new();
    formatter.render(output)
}

/// Extract type information from a JSON schema property
/// Handles various formats and never returns "unknown"
fn extract_type_info(prop: &serde_json::Value) -> String {
    // First try the 'type' field directly
    if let Some(type_str) = prop.get("type").and_then(|t| t.as_str()) {
        if type_str != "null" {
            return type_str.to_string();
        }
    }

    // Check if it's an array of types (one might be 'null')
    if let Some(type_array) = prop.get("type").and_then(|t| t.as_array()) {
        for t in type_array {
            if let Some(type_str) = t.as_str() {
                if type_str != "null" {
                    return type_str.to_string();
                }
            }
        }
    }

    // Check for ref types
    if let Some(ref_str) = prop.get("$ref").and_then(|r| r.as_str()) {
        // Extract the type name from the reference
        if let Some(type_name) = ref_str.split('/').next_back() {
            return type_name.to_string();
        }
        return "object".to_string();
    }

    // Check for enum types
    if prop.get("enum").is_some() {
        return "enum".to_string();
    }

    // Check for array types
    if prop.get("items").is_some() {
        let item_type = if let Some(items) = prop.get("items") {
            extract_type_info(items)
        } else {
            "any".to_string()
        };
        return format!("array[{item_type}]");
    }

    // Check for object types with properties
    if prop.get("properties").is_some() {
        return "object".to_string();
    }

    // Check for oneOf, anyOf, allOf
    for complex_type in ["oneOf", "anyOf", "allOf"] {
        if prop.get(complex_type).is_some() {
            return complex_type.to_string();
        }
    }

    // Default to "any" if no specific type found
    "any".to_string()
}
