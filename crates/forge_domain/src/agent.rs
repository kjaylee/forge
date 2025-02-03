use std::collections::HashMap;
use std::path::PathBuf;

use schemars::schema::RootSchema;
use serde::{Deserialize, Serialize};
use url::Url;

use crate::{Environment, Model, ModelId, ToolName};

#[derive(Clone, Debug, Serialize)]
pub struct SystemContext {
    pub env: Environment,
    pub tool_information: String,
    pub tool_supported: bool,
    pub custom_instructions: Option<String>,
    pub files: Vec<String>,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum ModelType {
    #[default]
    Primary,
    Secondary,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum PromptContent {
    Text(String),
    File(PathBuf),
}

impl From<String> for PromptContent {
    fn from(s: String) -> Self {
        PromptContent::Text(s)
    }
}

impl From<&str> for PromptContent {
    fn from(s: &str) -> Self {
        PromptContent::Text(s.to_string())
    }
}

pub struct Prompt<V> {
    pub template: PromptTemplate,
    pub variables: Schema<V>,
}

pub struct Schema<S> {
    pub schema: RootSchema,
    _marker: std::marker::PhantomData<S>,
}

pub enum PromptTemplate {
    File(PathBuf),
    Literal(String),
}

pub struct AgentId(String);

pub struct Agent {
    pub id: AgentId,
    pub provider: Provider,
    pub model: ModelId,
    pub description: String,
    pub system_prompt: Prompt<SystemContext>,
    pub user_prompt: Prompt<HashMap<String, String>>,
    pub tools: Vec<ToolName>,
    pub transforms: Vec<Transform>,
}

pub struct Provider(Url);

// TODO: Add more compression strategies
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

pub struct Arena {
    pub agents: Vec<Agent>,
    pub workflows: Option<Vec<Workflow>>,
    pub models: Vec<Model>,
    pub providers: Vec<Provider>,
    pub tools: Option<Vec<SmartTool<HashMap<String, String>>>>,
}

pub struct SmartTool<S> {
    pub name: ToolName,
    pub description: String,
    pub run: Routine,
    pub input: Schema<S>,
}

pub enum Routine {
    Agent(AgentId),
    Workflow(WorkflowId),
}

pub struct Handover {
    pub from: Routine,
    pub to: Routine,
}

pub struct WorkflowId(String);

pub struct Workflow {
    pub id: WorkflowId,
    pub description: String,
    pub handovers: Vec<Handover>,
}

pub enum Exit {
    Success,
    Failure,
}

impl Agent {
    pub fn new(name: impl Into<String>) -> Self {
        todo!()
    }
}
