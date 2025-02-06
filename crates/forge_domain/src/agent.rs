use std::collections::HashMap;
use std::path::PathBuf;

use derive_more::derive::Display;
use derive_setters::Setters;
use handlebars::Handlebars;
use schemars::schema::RootSchema;
use schemars::JsonSchema;
use serde::Serialize;
use serde_json::Value;

use crate::{Environment, Error, ModelId, Provider, ToolName};

#[derive(Debug, Default, Serialize, JsonSchema, Clone)]
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

    pub fn default_key() -> &'static str {
        "value"
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
                variables.add(Self::default_key(), value.to_string());
            }
            Value::Number(value) => {
                variables.add(Self::default_key(), value.to_string());
            }
            Value::String(value) => {
                variables.add(Self::default_key(), value);
            }
            Value::Array(values) => {
                variables.add(Self::default_key(), values);
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

#[derive(Debug, Serialize, Setters, Clone, JsonSchema)]
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

#[derive(Debug, Clone)]
pub struct Prompt<V> {
    pub template: PromptTemplate,
    pub variables: Schema<V>,
}

impl<V: Serialize> Prompt<V> {
    pub fn render(&self, ctx: &V) -> crate::Result<String> {
        let mut hb = Handlebars::new();
        hb.set_strict_mode(true);
        hb.register_escape_fn(|str| str.to_string());

        hb.render_template(self.template.as_str(), &ctx)
            .map_err(Error::Template)
    }
}

#[derive(Debug, Clone)]
pub struct Schema<S> {
    pub schema: RootSchema,
    _marker: std::marker::PhantomData<S>,
}

impl<S> Schema<S> {
    pub fn new(schema: RootSchema) -> Self {
        Self { schema, _marker: std::marker::PhantomData }
    }
}

#[derive(Debug, Clone)]
pub struct PromptTemplate(String);
impl PromptTemplate {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
    pub fn new(template: impl Into<String>) -> Self {
        Self(template.into())
    }
}

#[derive(Debug, Display, Eq, PartialEq, Hash, Clone)]
pub struct AgentId(String);

impl AgentId {
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }
}

#[derive(Debug)]
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

#[derive(Debug)]
/// Transformations that can be applied to the agent's context before sending it
/// upstream to the provider.
pub enum Transform {
    /// Compresses multiple assistant messages into a single message
    Assistant {
        input: String,
        output: String,
        agent_id: AgentId,
        token_limit: usize,
    },

    /// Works on the user prompt by enriching it with additional information
    User {
        agent_id: AgentId,
        input: String,
        output: String,
    },

    /// Intercepts the context and performs an operation without changing the
    /// context
    Tap { agent_id: AgentId, input: String },
}

impl Agent {
    pub fn new(_name: impl Into<String>) -> Self {
        todo!()
    }
}
