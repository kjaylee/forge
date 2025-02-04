use std::collections::HashMap;
use std::path::PathBuf;

use derive_more::derive::Display;
use schemars::schema::RootSchema;
use serde::Serialize;

use crate::{Environment, ModelId, Provider, ToolName};

#[derive(Default)]
pub struct Variables(HashMap<String, String>);

#[derive(Serialize)]
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
    pub fn render(&self, variables: &V) -> String {
        todo!()
    }
}

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

pub enum Transform {
    SuccessfulToolCalls(Action),
    FailedToolCalls(Action),
    Middle(Action),
    Agent(AgentId),
}

pub enum Action {
    Remove,
    Summarize,
    RemoveDuplicate,
}

impl Agent {
    pub fn new(name: impl Into<String>) -> Self {
        todo!()
    }
}
