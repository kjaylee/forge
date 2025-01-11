use inflector::Inflector;
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::ToolCallService;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ToolName(String);

impl ToolName {
    pub fn new(value: impl ToString) -> Self {
        ToolName(value.to_string())
    }
}

impl ToolName {
    pub fn into_string(self) -> String {
        self.0
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ToolName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub trait NamedTool {
    fn tool_name(&self) -> ToolName;
}

impl<T> NamedTool for T
where
    T: ToolCallService,
{
    fn tool_name(&self) -> ToolName {
        let name = std::any::type_name::<T>()
            .split("::")
            .last()
            .unwrap()
            .to_snake_case();
        ToolName(name)
    }
}