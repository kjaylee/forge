use derive_setters::Setters;
use forge_tool::ToolName;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{Error, Result};

/// Unique identifier for a using a tool
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct ToolUseId(pub(crate) String);

impl<A: ToString> From<A> for ToolUseId {
    fn from(value: A) -> Self {
        ToolUseId(value.to_string())
    }
}

/// Contains a part message for using a tool. This is received as a part of the
/// response from the model only when streaming is enabled.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize, Setters)]
#[setters(strip_option, into)]
pub struct ToolUsePart {
    /// Optional unique identifier that represents a single call to the tool
    /// use. NOTE: Not all models support a call ID for using a tool
    pub use_id: Option<ToolUseId>,
    pub name: Option<ToolName>,

    /// Arguments that need to be passed to the tool. NOTE: Not all tools
    /// require input
    pub argument_part: String,
}

/// Contains the full information about using a tool. This is received as a part
/// of the response from the model when streaming is disabled.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize, Setters)]
#[setters(strip_option, into)]
pub struct ToolUse {
    pub name: ToolName,
    pub use_id: Option<ToolUseId>,
    pub arguments: Value,
}

impl ToolUse {
    pub fn try_from_parts(parts: Vec<ToolUsePart>) -> Result<Self> {
        let mut tool_name = None;
        let mut tool_use_id = None;

        let mut input = String::new();
        for part in parts {
            if let Some(value) = part.name {
                tool_name = Some(value);
            }

            if let Some(value) = part.use_id {
                tool_use_id = Some(value);
            }

            input.push_str(&part.argument_part);
        }

        if let Some(tool_name) = tool_name {
            Ok(ToolUse {
                name: tool_name,
                use_id: tool_use_id,
                arguments: serde_json::from_str(&input)?,
            })
        } else {
            Err(Error::ToolUserMissingName)
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize, Setters)]
pub struct ToolResult {
    pub tool_name: ToolName,
    pub tool_use_id: Option<ToolUseId>,
    pub content: Value,
    pub is_error: bool,
}

impl ToolResult {
    pub fn new(tool_name: ToolName) -> ToolResult {
        Self {
            tool_name,
            tool_use_id: None,
            content: Value::default(),
            is_error: false,
        }
    }
}
