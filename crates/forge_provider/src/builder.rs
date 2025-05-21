// Context trait is needed for error handling in the provider implementations

use anyhow::{Context as _, Result};
use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Provider, ProviderService, ResultStream,
};
use reqwest::redirect::Policy;
use tokio_stream::StreamExt;

use crate::anthropic::Anthropic;
use crate::forge_provider::ForgeProvider;

pub struct Client {
    retry_status_codes: Vec<u16>,
    inner: InnerClient,
}

enum InnerClient {
    OpenAICompat(ForgeProvider),
    Anthropic(Anthropic),
}

impl Client {
    pub fn new(provider: Provider, retry_status_codes: Vec<u16>) -> Result<Self> {
        let client = reqwest::Client::builder()
            .read_timeout(std::time::Duration::from_secs(60))
            .pool_idle_timeout(std::time::Duration::from_secs(90))
            .pool_max_idle_per_host(5)
            .redirect(Policy::limited(10))
            .build()?;

        let inner = match &provider {
            Provider::OpenAI { url, .. } => InnerClient::OpenAICompat(
                ForgeProvider::builder()
                    .client(client)
                    .provider(provider.clone())
                    .build()
                    .with_context(|| format!("Failed to initialize: {url}"))?,
            ),

            Provider::Anthropic { url, key } => InnerClient::Anthropic(
                Anthropic::builder()
                    .client(client)
                    .api_key(key.to_string())
                    .base_url(url.clone())
                    .anthropic_version("2023-06-01".to_string())
                    .build()
                    .with_context(|| {
                        format!("Failed to initialize Anthropic client with URL: {url}")
                    })?,
            ),
        };
        Ok(Self { inner, retry_status_codes })
    }
}

#[async_trait::async_trait]
impl ProviderService for Client {
    async fn chat(
        &self,
        model: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        let chat_stream = match &self.inner {
            InnerClient::OpenAICompat(provider) => provider.chat(model, context).await,
            InnerClient::Anthropic(provider) => provider.chat(model, context).await,
        }?;
        let retry_status_codes = self.retry_status_codes.clone();
        Ok(Box::pin(chat_stream.map(move |item| {
            item.map_err(|e| provider_error(e, retry_status_codes.clone()))
        })))
    }

    async fn models(&self) -> anyhow::Result<Vec<Model>> {
        let retry_status_codes = self.retry_status_codes.clone();
        Ok(match &self.inner {
            InnerClient::OpenAICompat(provider) => provider.models().await,
            InnerClient::Anthropic(provider) => provider.models().await,
        }
        .map_err(|e| provider_error(e, retry_status_codes))?)
    }
}

fn provider_error(error: anyhow::Error, retry_status_codes: Vec<u16>) -> anyhow::Error {
    if let Some(code) = get_status_code(&error) {
        if retry_status_codes.contains(&code) {
            return forge_domain::Error::Retryable(error).into();
        }
    }

    if is_transport_error(&error) {
        return forge_domain::Error::Retryable(error).into();
    }

    error
}

fn get_status_code(error: &anyhow::Error) -> Option<u16> {
    error
        .downcast_ref::<crate::error::Error>()
        .and_then(|error| match error {
            crate::error::Error::Api(error) => {
                error.code.as_ref().and_then(|code| code.as_number())
            }
            crate::error::Error::Reqwest(reqwest_eventsource::Error::InvalidStatusCode(
                code,
                _,
            )) => Some(code.as_u16()),
            _ => None,
        })
}

fn is_transport_error(error: &anyhow::Error) -> bool {
    error
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
