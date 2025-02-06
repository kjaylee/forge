#![allow(dead_code)]

use anyhow::Result;
use url::Url;

use crate::{ChatCompletionMessage, Context, Model, ModelId, Parameters, ResultStream};

#[async_trait::async_trait]
pub trait ProviderService: Send + Sync + 'static {
    async fn chat(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error>;
    async fn models(&self) -> Result<Vec<Model>>;
    async fn parameters(&self, model: &ModelId) -> Result<Parameters>;
}

#[derive(Debug, Clone)]
pub struct Provider(Url);

impl Provider {
    pub fn try_new(url: impl Into<String>) -> Result<Self> {
        let url = Url::parse(&url.into())?;
        Ok(Self(url))
    }
}
