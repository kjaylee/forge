use forge_api::ToolDefinition;

/// Formats the list of tools for display in the shell UI, showing only the tool
/// name as a blue bold heading with numbering for each tool.
pub fn format_tools(tools: &[ToolDefinition]) -> String {
    let mut output = String::new();

    for (i, tool) in tools.iter().enumerate() {
        // Add numbered tool name as plain text
        output.push_str(&format!("{}.  {}", i + 1, tool.name));

        // Add newline between tools
        if i < tools.len() - 1 {
            output.push('\n');
        }
    }

    output
}
