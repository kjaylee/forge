use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Enum representing all possible tool output types.
///
/// This enum contains variants for each type of output that can be returned from
/// tools in the application. Each variant corresponds to the output type for a
/// specific tool.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "tool", content = "result")]
pub enum ToolOutput {
    /// Output from the file read tool
    #[serde(rename = "forge_tool_fs_read")]
    FSRead(FSReadOutput),

    /// Output from the file write tool
    #[serde(rename = "forge_tool_fs_create")]
    FSWrite(FSWriteOutput),

    /// Output from the file search tool
    #[serde(rename = "forge_tool_fs_search")]
    FSSearch(FSSearchOutput),

    /// Output from the file remove tool
    #[serde(rename = "forge_tool_fs_remove")]
    FSRemove(FSRemoveOutput),

    /// Output from the file patch tool
    #[serde(rename = "forge_tool_fs_patch")]
    FSPatch(FSPatchOutput),

    /// Output from the file undo tool
    #[serde(rename = "forge_tool_fs_undo")]
    FSUndo(FSUndoOutput),

    /// Output from the shell command tool
    #[serde(rename = "forge_tool_process_shell")]
    Shell(ShellOutput),

    /// Output from the net fetch tool
    #[serde(rename = "forge_tool_net_fetch")]
    NetFetch(NetFetchOutput),

    /// Output from the followup tool
    #[serde(rename = "forge_tool_followup")]
    Followup(FollowupOutput),

    /// Output from the completion tool
    #[serde(rename = "forge_tool_attempt_completion")]
    AttemptCompletion(AttemptCompletionOutput),
}

/// Output type for the file read tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FSReadOutput {
    /// The path of the file that was read
    pub path: String,
    
    /// If a character range was used, the starting position
    #[serde(skip_serializing_if = "Option::is_none")]
    pub start_char: Option<u64>,
    
    /// If a character range was used, the ending position
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_char: Option<u64>,
    
    /// The total number of characters in the file
    #[serde(skip_serializing_if = "Option::is_none")]
    pub total_chars: Option<u64>,
    
    /// The content that was read from the file
    pub content: String,
}

/// Output type for the file write tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FSWriteOutput {
    /// The path of the file that was written
    pub path: String,
    
    /// Whether the file was created or overwritten
    pub operation: FileOperation,
    
    /// The total number of characters written to the file
    pub total_chars: usize,
    
    /// Optional warning message if syntax issues were detected
    #[serde(skip_serializing_if = "Option::is_none")]
    pub warning: Option<String>,
    
    /// Diff output showing changes if the file was overwritten
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diff: Option<String>,
}

/// Types of file operations
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema, PartialEq)]
#[serde(rename_all = "UPPERCASE")]
pub enum FileOperation {
    /// File was created
    Create,
    
    /// File was overwritten
    Overwrite,
    
    /// File was removed
    Remove,
    
    /// File was patched/modified
    Patch,
    
    /// File was reverted to a previous state
    Undo,
}

/// Output type for the file search tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FSSearchOutput {
    /// The path that was searched
    pub path: String,
    
    /// The regex pattern that was searched for, if any
    #[serde(skip_serializing_if = "Option::is_none")]
    pub regex: Option<String>,
    
    /// The file pattern that was used to filter files, if any
    #[serde(skip_serializing_if = "Option::is_none")]
    pub file_pattern: Option<String>,
    
    /// The matches that were found
    pub matches: Vec<SearchMatch>,
    
    /// Total number of matches found
    pub total_matches: usize,
}

/// A single match from a file search
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SearchMatch {
    /// The file path where the match was found
    pub file: String,
    
    /// The line number where the match was found, if applicable
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    
    /// The matched content
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content: Option<String>,
    
    /// Content before the match for context
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context_before: Option<String>,
    
    /// Content after the match for context
    #[serde(skip_serializing_if = "Option::is_none")]
    pub context_after: Option<String>,
}

/// Output type for the file remove tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FSRemoveOutput {
    /// The path of the file that was removed
    pub path: String,
    
    /// Whether the operation was successful
    pub success: bool,
    
    /// Additional details about the operation
    #[serde(skip_serializing_if = "Option::is_none")]
    pub details: Option<String>,
}

/// Output type for the file patch tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FSPatchOutput {
    /// The path of the file that was patched
    pub path: String,
    
    /// The total number of characters in the file after patching
    pub total_chars: usize,
    
    /// Optional warning message if syntax issues were detected
    #[serde(skip_serializing_if = "Option::is_none")]
    pub warning: Option<String>,
    
    /// Diff output showing changes
    pub diff: String,
}

/// Output type for the file undo tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FSUndoOutput {
    /// The path of the file that was reverted
    pub path: String,
    
    /// Whether the operation was successful
    pub success: bool,
    
    /// Additional details about the operation
    pub details: String,
}

/// Output type for the shell command tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ShellOutput {
    /// The command that was executed
    pub command: String,
    
    /// The working directory where the command was executed
    pub cwd: String,
    
    /// The exit code of the command
    pub exit_code: i32,
    
    /// The standard output of the command
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout: Option<String>,
    
    /// The standard error output of the command
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stderr: Option<String>,
}

/// Output type for the net fetch tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct NetFetchOutput {
    /// The URL that was fetched
    pub url: String,
    
    /// Whether the request was successful
    pub success: bool,
    
    /// The content that was fetched
    pub content: String,
    
    /// The content type of the response
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_type: Option<String>,
    
    /// Whether the content was returned in raw format
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw: Option<bool>,
}

/// Output type for the followup tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FollowupOutput {
    /// The user's response to the followup
    pub response: String,
    
    /// The selected options if multiple selection was enabled
    #[serde(skip_serializing_if = "Option::is_none")]
    pub selected_options: Option<Vec<String>>,
}

/// Output type for the completion tool
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct AttemptCompletionOutput {
    /// The final result text
    pub result: String,
}
