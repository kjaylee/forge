use derive_more::derive::Display;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, Serialize, Setters)]
#[setters(into, strip_option)]
pub struct Model {
    pub id: ModelId,
    pub name: Option<String>,
    pub description: Option<String>,
    pub context_length: Option<u64>,
    // TODO: add provider information to the model
    pub tools_supported: Option<bool>,
}

impl Model {
    pub fn new(id: ModelId) -> Self {
        Self {
            id,
            name: None,
            description: None,
            context_length: None,
            tools_supported: None,
        }
    }
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct Parameters {
    pub tool_supported: bool,
}

impl Parameters {
    pub fn new(tool_supported: bool) -> Self {
        Self { tool_supported }
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, Hash, Eq, Display)]
#[serde(transparent)]
pub struct ModelId(String);

impl ModelId {
    pub fn new<T: Into<String>>(id: T) -> Self {
        Self(id.into())
    }
}

impl ModelId {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
