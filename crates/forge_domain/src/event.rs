use derive_setters::Setters;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{NamedTool, ToolName};

// We'll use simple strings for JSON schema compatibility
#[derive(Debug, Deserialize, Serialize, Clone, Setters)]
pub struct Event {
    pub id: String,
    pub name: String,
    pub value: Value,
    pub timestamp: String,
}

#[derive(Debug, JsonSchema, Deserialize, Serialize, Clone)]
pub struct EventMessage {
    pub name: String,
    pub value: Value,
}

impl From<EventMessage> for Event {
    fn from(value: EventMessage) -> Self {
        Self::new(value.name, value.value)
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, Setters)]
pub struct EventContext {
    event: Event,
    suggestions: Vec<String>,
    current_time: String,
}

impl EventContext {
    pub fn new(event: Event) -> Self {
        Self {
            event,
            suggestions: Default::default(),
            current_time: chrono::Local::now()
                .format("%Y-%m-%d %H:%M:%S %:z")
                .to_string(),
        }
    }
}

impl NamedTool for Event {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_event_dispatch")
    }
}

impl Event {
    pub fn new<V: Into<Value>>(name: impl ToString, value: V) -> Self {
        let id = uuid::Uuid::new_v4().to_string();
        let timestamp = chrono::Utc::now().to_rfc3339();

        Self { id, name: name.to_string(), value: value.into(), timestamp }
    }
}
