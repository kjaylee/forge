// Context trait is needed for error handling in the provider implementations

use anyhow::Result;
use derive_setters::Setters;
use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Parameters, Provider, ProviderService,
    ResultStream,
};

use crate::anthropic::Anthropic;
use crate::open_router::OpenRouter;

// ProviderBuilder moved from lib.rs
#[derive(Debug, Setters)]
#[setters(strip_option)]
pub struct ClientBuilder {
    provider: Provider,
    api_key: Option<String>,
}

pub enum Client {
    OpenAICompat(OpenRouter),
    Anthropic(Anthropic),
}

impl ClientBuilder {
    pub fn new(provider: Provider) -> Self {
        Self { provider, api_key: None }
    }

    pub fn build(self) -> Result<Client> {
        let provider = self.provider;

        let api_key = self
            .api_key
            .ok_or_else(|| anyhow::anyhow!("API key is required for provider: {}", provider))?;

        match provider {
            forge_domain::Provider::OpenAI { url } => Ok(Client::OpenAICompat(
                OpenRouter::builder()
                    .url(url)
                    .api_key(Some(api_key))
                    .build()?,
            )),

            forge_domain::Provider::Anthropic => Ok(Client::Anthropic(
                Anthropic::builder().api_key(api_key).build()?,
            )),
        }
    }
}

#[async_trait::async_trait]
impl ProviderService for Client {
    async fn chat(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        match self {
            Client::OpenAICompat(provider) => provider.chat(id, context).await,
            Client::Anthropic(provider) => provider.chat(id, context).await,
        }
    }

    async fn models(&self) -> anyhow::Result<Vec<Model>> {
        match self {
            Client::OpenAICompat(provider) => provider.models().await,
            Client::Anthropic(provider) => provider.models().await,
        }
    }

    async fn parameters(&self, model: &ModelId) -> anyhow::Result<Parameters> {
        match self {
            Client::OpenAICompat(provider) => provider.parameters(model).await,
            Client::Anthropic(provider) => provider.parameters(model).await,
        }
    }
}
