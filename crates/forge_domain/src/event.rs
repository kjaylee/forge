use std::collections::HashMap;
use std::fmt::Display;

use derive_setters::Setters;
use schemars::{schema_for, JsonSchema};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{NamedTool, ToolCallFull, ToolDefinition, ToolName};

// We'll use simple strings for JSON schema compatibility
#[derive(Debug, Deserialize, Serialize, Clone, Setters)]
pub struct Event {
    pub id: String,
    pub name: Name,
    pub value: Value,
    pub timestamp: String,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
#[serde(transparent)]
pub struct Name {
    parts: Vec<String>,
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.parts.join("/"))
    }
}

impl<T, S> From<T> for Name
where
    T: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    fn from(value: T) -> Self {
        Self {
            parts: value.into_iter().map(|s| s.as_ref().to_string()).collect(),
        }
    }
}

impl Name {
    // FIXME: Handle unsupported characters
    pub fn parse(value: impl ToString) -> Self {
        let parts = value
            .to_string()
            .split('/')
            .map(|s| s.to_string())
            .collect();
        Self { parts }
    }
}

#[derive(Debug, JsonSchema, Deserialize, Serialize, Clone)]
pub struct EventMessage {
    pub name: String,
    pub value: Value,
}

impl From<EventMessage> for Event {
    fn from(value: EventMessage) -> Self {
        let name = Name::parse(value.name.clone());
        Self::new(name, value.value)
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, Setters)]
pub struct EventContext {
    event: Event,
    suggestions: Vec<String>,
    variables: HashMap<String, Value>,
    current_time: String,
}

impl EventContext {
    pub fn new(event: Event) -> Self {
        // Get current date and time in format YYYY-MM-DD HH:MM:SS
        let current_time = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();

        Self {
            event,
            suggestions: Default::default(),
            variables: Default::default(),
            current_time,
        }
    }
}

impl NamedTool for Event {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_event_dispatch")
    }
}

impl Event {
    pub fn tool_definition() -> ToolDefinition {
        ToolDefinition {
            name: Self::tool_name(),
            description: "Dispatches an event with the provided name and value".to_string(),
            input_schema: schema_for!(EventMessage),
            output_schema: None,
        }
    }

    pub fn parse(tool_call: &ToolCallFull) -> Option<Self> {
        if tool_call.name != Self::tool_definition().name {
            return None;
        }
        let message: Option<EventMessage> =
            serde_json::from_value(tool_call.arguments.clone()).ok();

        message.map(|message| message.into())
    }

    // New constructor that takes vector directly
    pub fn new<N: Into<Name>, V: Into<Value>>(name: N, value: V) -> Self {
        let id = uuid::Uuid::new_v4().to_string();
        let timestamp = chrono::Utc::now().to_rfc3339();

        Self { id, name: name.into(), value: value.into(), timestamp }
    }
}

// Add Display trait for easy string conversion
impl Display for Event {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

// Add PartialEq trait for comparison with strings (for compatibility)
impl PartialEq<str> for Event {
    fn eq(&self, other: &str) -> bool {
        self.name.to_string() == other
    }
}

impl PartialEq<&str> for Event {
    fn eq(&self, other: &&str) -> bool {
        self.name.to_string() == *other
    }
}
