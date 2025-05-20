// Context trait is needed for error handling in the provider implementations

use anyhow::{Context as _, Result};
use derive_more::{Display, From};
use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Provider, ProviderError, ProviderService,
    ResultStream,
};
use reqwest::redirect::Policy;
use thiserror::Error;
use tokio_stream::StreamExt;

use crate::anthropic::Anthropic;
use crate::forge_provider::ForgeProvider;

pub enum Client {
    OpenAICompat(ForgeProvider),
    Anthropic(Anthropic),
}

impl Client {
    pub fn new(provider: Provider) -> Result<Self> {
        let client = reqwest::Client::builder()
            .read_timeout(std::time::Duration::from_secs(60))
            .pool_idle_timeout(std::time::Duration::from_secs(90))
            .pool_max_idle_per_host(5)
            .redirect(Policy::limited(10))
            .build()?;

        match &provider {
            Provider::OpenAI { url, .. } => Ok(Client::OpenAICompat(
                ForgeProvider::builder()
                    .client(client)
                    .provider(provider.clone())
                    .build()
                    .with_context(|| format!("Failed to initialize: {url}"))?,
            )),

            Provider::Anthropic { url, key } => Ok(Client::Anthropic(
                Anthropic::builder()
                    .client(client)
                    .api_key(key.to_string())
                    .base_url(url.clone())
                    .anthropic_version("2023-06-01".to_string())
                    .build()
                    .with_context(|| {
                        format!("Failed to initialize Anthropic client with URL: {url}")
                    })?,
            )),
        }
    }
}

#[async_trait::async_trait]
impl ProviderService for Client {
    type Error = ForgeProviderError;
    async fn chat(
        &self,
        model: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, Self::Error> {
        let chat_stream = match self {
            Client::OpenAICompat(provider) => provider.chat(model, context).await,
            Client::Anthropic(provider) => provider.chat(model, context).await,
        }?;

        Ok(Box::pin(
            chat_stream.map(|item| item.map_err(ForgeProviderError::from)),
        ))
    }

    async fn models(&self) -> Result<Vec<Model>, Self::Error> {
        Ok(match self {
            Client::OpenAICompat(provider) => provider.models().await,
            Client::Anthropic(provider) => provider.models().await,
        }?)
    }
}

#[derive(Display, Debug, Error, From)]
pub struct ForgeProviderError(anyhow::Error);

impl ProviderError for ForgeProviderError {
    fn status_code(&self) -> Option<u16> {
        self.0
            .downcast_ref::<crate::error::Error>()
            .and_then(|error| match error {
                crate::error::Error::Api(error) => {
                    error.code.as_ref().and_then(|code| code.as_number())
                }
                crate::error::Error::Reqwest(reqwest_eventsource::Error::InvalidStatusCode(
                    code,
                    _,
                )) => Some(code.as_u16()),
                crate::error::Error::InvalidStatusCode(code) => Some(*code),
                _ => None,
            })
    }

    fn is_transport_error(&self) -> bool {
        self.0
            .downcast_ref::<crate::error::Error>()
            .is_some_and(|error| match error {
                crate::error::Error::Api(error) => error
                    .code
                    .as_ref()
                    .and_then(|code| code.as_str())
                    .is_some_and(|code| {
                        ["ERR_STREAM_PREMATURE_CLOSE", "ECONNRESET", "ETIMEDOUT"]
                            .into_iter()
                            .any(|message| message == code)
                    }),
                crate::error::Error::Reqwest(error) => {
                    matches!(error, reqwest_eventsource::Error::Transport(_))
                }
                _ => false,
            })
    }
}
