use forge_api::Event;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::mode::ForgeMode;

// Constants for event names
pub const EVENT_USER_TASK_INIT: &str = "task_init";
pub const EVENT_USER_TASK_UPDATE: &str = "task_update";
pub const EVENT_TITLE: &str = "ui/title";

#[derive(Serialize, Deserialize)]
pub struct EventBuilder {
    pub name: String,
    pub value: Value,
}

impl EventBuilder {
    pub fn new<V: Into<Value>>(name: impl ToString, value: V) -> Self {
        Self { name: name.to_string(), value: value.into() }
    }

    pub fn into_event(self, mode: Option<&ForgeMode>) -> Event {
        // Create event with mode prefix if available
        let prefix = mode
            .map(|m| m.to_string().to_lowercase())
            .unwrap_or_else(|| "default".to_string());

        let name_parts = vec![prefix, "user".to_string(), self.name];
        Event::new(name_parts, self.value)
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_event_builder_with_mode() {
        let fixture_mode = ForgeMode::new("act");
        let fixture_builder = EventBuilder::new("task_update", "test message");

        let actual = fixture_builder.into_event(Some(&fixture_mode));

        assert_eq!(actual.name.to_string(), "act/user/task_update");
        assert_eq!(actual.value.as_str().unwrap(), "test message");
    }

    #[test]
    fn test_event_builder_without_mode() {
        let fixture_builder = EventBuilder::new("task_init", "initial message");

        let actual = fixture_builder.into_event(None);

        assert_eq!(actual.name.to_string(), "default/user/task_init");
        assert_eq!(actual.value.as_str().unwrap(), "initial message");
    }
}
