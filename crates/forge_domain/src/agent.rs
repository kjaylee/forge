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

pub struct Agent<S, U> {
    pub model: Vec<Model>,
    pub name: String,
    pub description: Option<String>,
    pub system_prompt: Prompt<S>,
    pub user_prompt: Prompt<U>,
}

pub struct ModelId(String);

pub struct Model {
    pub id: ModelId,
    pub provider: Provider,
}

pub struct Provider {
    base_url: Url,
}
