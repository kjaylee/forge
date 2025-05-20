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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::{AnthropicApiError, ApiError, Error, ErrorCode};
    use pretty_assertions::assert_eq;

    fn create_api_error_with_code(code: ErrorCode) -> anyhow::Error {
        let api_error = ApiError {
            error: None,
            message: Some("Test message".to_string()),
            errno: None,
            code: Some(code),
            metadata: Default::default(),
            syscall: None,
            type_of: None,
            param: None,
        };
        Error::Api(api_error).into()
    }

    // Helper function to create a ForgeProviderError with an InvalidStatusCode error
    fn create_invalid_status_code_error(code: u16) -> ForgeProviderError {
        ForgeProviderError(Error::InvalidStatusCode(code).into())
    }

    // Helper function to create ForgeProviderError with an API error containing a specific error code string
    fn create_api_string_error(code_str: &str) -> ForgeProviderError {
        ForgeProviderError(create_api_error_with_code(ErrorCode::String(code_str.to_string())))
    }

    // Helper function to create ForgeProviderError with a SerdeJson error
    fn create_serde_json_error() -> ForgeProviderError {
        let error = serde_json::from_str::<serde_json::Value>("{invalid: json}").unwrap_err();
        ForgeProviderError(Error::SerdeJson(error).into())
    }

    #[test]
    fn test_status_code() {
        // Test with API error with numeric code
        let error = ForgeProviderError(create_api_error_with_code(ErrorCode::Number(404)));
        assert_eq!(error.status_code(), Some(404));

        // Test with API error with string code containing a number
        let error = ForgeProviderError(create_api_error_with_code(ErrorCode::String("500".to_string())));
        assert_eq!(error.status_code(), Some(500));

        // Test with API error with non-numeric string code
        let error = create_api_string_error("ERR_STREAM_PREMATURE_CLOSE");
        assert_eq!(error.status_code(), None);

        // Test with InvalidStatusCode error
        let error = create_invalid_status_code_error(429);
        assert_eq!(error.status_code(), Some(429));

        // Test with other error types
        let error = create_serde_json_error();
        assert_eq!(error.status_code(), None);

        let error = ForgeProviderError(Error::ToolCallMissingName.into());
        assert_eq!(error.status_code(), None);

        let error = ForgeProviderError(Error::Anthropic(AnthropicApiError::OverloadedError {
            message: "Test message".to_string(),
        }).into());
        assert_eq!(error.status_code(), None);
    }

    #[test]
    fn test_is_transport_error() {
        // Test with API error with transport error code
        let error = create_api_string_error("ERR_STREAM_PREMATURE_CLOSE");
        assert!(error.is_transport_error());

        let error = create_api_string_error("ECONNRESET");
        assert!(error.is_transport_error());

        let error = create_api_string_error("ETIMEDOUT");
        assert!(error.is_transport_error());

        // Test with API error with non-transport error code
        let error = create_api_string_error("SOME_OTHER_ERROR");
        assert!(!error.is_transport_error());

        // Test with other error types
        let error = create_serde_json_error();
        assert!(!error.is_transport_error());

        let error = ForgeProviderError(Error::ToolCallMissingName.into());
        assert!(!error.is_transport_error());

        let error = ForgeProviderError(Error::Anthropic(AnthropicApiError::OverloadedError {
            message: "Test message".to_string(),
        }).into());
        assert!(!error.is_transport_error());

        let error = create_invalid_status_code_error(500);
        assert!(!error.is_transport_error());
    }
}