use std::path::PathBuf;

use url::Url;

pub struct Prompt<T> {
    template: PromptTemplate,
    marker: std::marker::PhantomData<T>,
}

pub enum PromptTemplate {
    File(PathBuf),
    Literal(String),
}

pub struct AgentId(String);

pub struct Agent<S, U> {
    pub id: AgentId,
    pub model: Vec<Model>,
    pub description: String,
    pub system_prompt: Prompt<S>,
    pub user_prompt: Prompt<U>,
    pub tools: Vec<Tool>,
    pub transforms: Vec<Transform>,
}

pub enum Tool {
    FileRead,
    FileWrite,
    ExecuteCommand,
    EnvironmentRead,
}

pub struct ModelId(String);

pub struct Model {
    pub id: ModelId,
    pub provider: Provider,
}

pub struct Provider {
    pub base_url: Url,
}

// TODO: Add more compression strategies
pub enum Transform {
    SuccessfulToolCalls(Action),
    FailedToolCalls(Action),
    MiddleOut,
    Agent(AgentId),
}

pub enum Action {
    Remove,
    Summarize,
    RemoveDuplicate,
}
