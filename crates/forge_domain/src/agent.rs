use std::collections::HashMap;
use std::path::PathBuf;

use derive_more::derive::Display;
use derive_setters::Setters;
use schemars::schema::RootSchema;
use serde::Serialize;
use serde_json::Value;

use crate::{Environment, ModelId, Provider, ToolName};

#[derive(Default, Serialize)]
pub struct Variables(HashMap<String, Value>);
impl Variables {
    pub fn add(&mut self, key: impl Into<String>, value: impl Into<Value>) {
        self.0.insert(key.into(), value.into());
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        self.0.get(key)
    }

    pub fn merge(self, other: Self) -> Self {
        let mut merged = self;
        merged.0.extend(other.0);
        merged
    }
}

impl From<Vec<Variables>> for Variables {
    fn from(value: Vec<Variables>) -> Self {
        value
            .into_iter()
            .reduce(|a, b| a.merge(b))
            .unwrap_or_default()
    }
}

impl From<Value> for Variables {
    fn from(value: Value) -> Self {
        let mut variables = Variables::default();
        match value {
            Value::Null => {}
            Value::Bool(value) => {
                variables.add("value", value.to_string());
            }
            Value::Number(value) => {
                variables.add("value", value.to_string());
            }
            Value::String(value) => {
                variables.add("value", value);
            }
            Value::Array(values) => {
                variables.add("value", values);
            }
            Value::Object(map) => {
                for (key, value) in map {
                    variables.add(key, value);
                }
            }
        };

        variables
    }
}

#[derive(Serialize, Setters, Clone)]
pub struct SystemContext {
    pub env: Environment,
    pub tool_information: String,
    pub tool_supported: bool,
    pub custom_instructions: Option<String>,
    pub files: Vec<String>,
}

pub enum PromptContent {
    Text(String),
    File(PathBuf),
}

pub struct Prompt<V> {
    pub template: PromptTemplate,
    pub variables: Schema<V>,
}

impl<V> Prompt<V> {
    pub fn render(&self, _variables: &V) -> String {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct Schema<S> {
    pub schema: RootSchema,
    _marker: std::marker::PhantomData<S>,
}

pub enum PromptTemplate {
    File(PathBuf),
    Literal(String),
}

#[derive(Debug, Display, Eq, PartialEq, Hash, Clone)]
pub struct AgentId(String);

pub struct Agent {
    pub id: AgentId,
    pub provider: Provider,
    pub model: ModelId,
    pub description: String,
    pub system_prompt: Prompt<SystemContext>,
    pub user_prompt: Prompt<Variables>,
    pub tools: Vec<ToolName>,
    pub transforms: Vec<Transform>,
}

/// Possible use cases for transforms:
/// - Summarization (TokenLimit)
///   - Remove all, except first, and add summary as an assistant message
/// - Enhance user prompt
///   - Add additional meta information to the last user prompt
/// - Standard middle-out implementation like in Open Router NOTE: The
///   transforms are applied in the order they are defined (0th to last)
pub enum Transform {
    Summarize {
        input: String,
        agent_id: AgentId,
        token_limit: usize,
    },

    EnhanceUserPrompt {
        agent_id: AgentId,
        input: String,
    },
}

impl Agent {
    pub fn new(_name: impl Into<String>) -> Self {
        todo!()
    }
}
