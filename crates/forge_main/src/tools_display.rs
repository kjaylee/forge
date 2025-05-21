use colored::Colorize;
use forge_api::ToolDefinition;
use forge_display::markdown::MarkdownFormat;

/// Formats the list of tools for display in the shell UI, showing only the tool name
/// as a blue bold heading with numbering for each tool.
pub fn format_tools(tools: &[ToolDefinition]) -> String {
    let mut output = String::new();

    for (i, tool) in tools.iter().enumerate() {
        // Format number and tool name as blue bold
        let number = format!("{}", i + 1).blue().bold();
        let name = tool.name.to_string().blue().bold();

        // Add numbered tool name, with backticks around name to prevent rendering as hyperlink
        output.push_str(&format!("{number}. `{name}`"));

        // Add newline between tools
        if i < tools.len() - 1 {
            output.push_str("\n");
        }
    }

    // Use the markdown formatter to render the final output
    let formatter = MarkdownFormat::new();
    formatter.render(output)
}
