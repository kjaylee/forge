use derive_setters::Setters;
use schemars::{schema_for, JsonSchema};
use serde::{Deserialize, Serialize};

use crate::{NamedTool, ToolCallFull, ToolDefinition, ToolName};

#[derive(Debug, JsonSchema, Deserialize, Serialize, Clone)]
pub struct DispatchEvent {
    pub name: String,
    pub value: String,
}

#[derive(Clone, Serialize, Deserialize, Debug, Setters)]
pub struct UserContext {
    event: DispatchEvent,
    suggestions: Vec<String>,
}

impl UserContext {
    pub fn new(event: DispatchEvent) -> Self {
        Self { event, suggestions: Default::default() }
    }
}

impl NamedTool for DispatchEvent {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_event_dispatch")
    }
}

impl DispatchEvent {
    pub fn tool_definition() -> ToolDefinition {
        ToolDefinition {
            name: Self::tool_name(),
            description: "Dispatches an event with the provided name and value".to_string(),
            input_schema: schema_for!(Self),
            output_schema: None,
        }
    }

    pub fn parse(tool_call: &ToolCallFull) -> Option<Self> {
        if tool_call.name != Self::tool_definition().name {
            return None;
        }
        serde_json::from_value(tool_call.arguments.clone()).ok()
    }

    pub fn new(name: impl ToString, value: impl ToString) -> Self {
        Self { name: name.to_string(), value: value.to_string() }
    }

    pub fn task_init(value: impl ToString) -> Self {
        Self::new(Self::USER_TASK_INIT, value)
    }

    pub fn task_update(value: impl ToString) -> Self {
        Self::new(Self::USER_TASK_UPDATE, value)
    }

    pub const USER_TASK_INIT: &'static str = "user_task_init";
    pub const USER_TASK_UPDATE: &'static str = "user_task_update";
}
