// Context trait is needed for error handling in the provider implementations

use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Parameters, Provider, ProviderService,
    ResultStream,
};

use crate::anthropic::Anthropic;
use crate::open_router::{OpenRouter, Provider as OpenRouterProvider};

// Configuration data needed for provider initialization
#[derive(Clone)]
pub struct ProviderConfig {
    pub api_key: String,
    pub url: String,
}

// ProviderBuilder moved from lib.rs
#[derive(Debug)]
pub struct ClientBuilder {
    url: String,
    api_key: Option<String>,
}

impl ClientBuilder {
    pub fn from_url<S: Into<String>>(url: S) -> Self {
        Self { url: url.into(), api_key: None }
    }

    pub fn with_key<S: Into<String>>(mut self, key: S) -> Self {
        self.api_key = Some(key.into());
        self
    }

    pub fn build(self) -> Result<Client, anyhow::Error> {
        let provider = Provider::from_url(&self.url)
            .ok_or_else(|| anyhow::anyhow!("Failed to detect provider from URL: {}", self.url))?;
        let api_key = self
            .api_key
            .ok_or_else(|| anyhow::anyhow!("API key is required for provider: {}", provider))?;

        // Create a Provider with configuration
        let config = ProviderConfig { api_key, url: self.url };

        Ok(create_configured_provider(provider, config))
    }
}

// We can't implement traits for types from other crates directly,
// so we'll use a wrapper type instead

// Extension trait for Provider to add configuration
pub trait ProviderExt {
    fn with_config(self, config: ProviderConfig) -> Client;
}

// A wrapper that combines the Provider enum with its configuration
#[derive(Clone)]
pub struct Client {
    provider: Provider,
    config: ProviderConfig,
}

// Helper function to create a ConfiguredProvider without using an extension
// trait
pub fn create_configured_provider(provider: Provider, config: ProviderConfig) -> Client {
    Client { provider, config }
}

impl Client {
    pub fn new(provider: Provider, config: ProviderConfig) -> Self {
        Self { provider, config }
    }

    pub fn provider(&self) -> &Provider {
        &self.provider
    }

    // Additional helper methods
    pub fn api_key(&self) -> &str {
        &self.config.api_key
    }

    pub fn url(&self) -> &str {
        &self.config.url
    }

    /// Returns whether this provider supports function calls/tools
    pub fn supports_tools(&self) -> bool {
        // This is a simplified implementation - in practice you might want to check
        // this dynamically
        match self.provider {
            Provider::OpenAI | Provider::OpenRouter | Provider::Anthropic => true,
            Provider::Antinomy => true,
        }
    }
}

#[async_trait::async_trait]
impl ProviderService for Client {
    async fn chat(
        &self,
        model_id: &ModelId,
        request: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        match self.provider {
            Provider::Antinomy => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::Antinomy)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.chat(model_id, request).await
            }
            Provider::OpenRouter => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenRouter)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.chat(model_id, request).await
            }
            Provider::OpenAI => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenAI)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.chat(model_id, request).await
            }
            Provider::Anthropic => {
                let provider = Anthropic::builder()
                    .api_key(self.config.api_key.clone())
                    .base_url(self.config.url.clone())
                    .build()?;
                provider.chat(model_id, request).await
            }
        }
    }

    async fn models(&self) -> anyhow::Result<Vec<Model>> {
        match self.provider {
            Provider::Antinomy => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::Antinomy)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.models().await
            }
            Provider::OpenRouter => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenRouter)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.models().await
            }
            Provider::OpenAI => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenAI)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.models().await
            }
            Provider::Anthropic => {
                let provider = Anthropic::builder()
                    .api_key(self.config.api_key.clone())
                    .base_url(self.config.url.clone())
                    .build()?;
                provider.models().await
            }
        }
    }

    async fn parameters(&self, model: &ModelId) -> anyhow::Result<Parameters> {
        match self.provider {
            Provider::Antinomy => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::Antinomy)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.parameters(model).await
            }
            Provider::OpenRouter => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenRouter)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.parameters(model).await
            }
            Provider::OpenAI => {
                let provider = OpenRouter::builder()
                    .provider(OpenRouterProvider::OpenAI)
                    .api_key(self.config.api_key.clone())
                    .build()?;
                provider.parameters(model).await
            }
            Provider::Anthropic => {
                let provider = Anthropic::builder()
                    .api_key(self.config.api_key.clone())
                    .base_url(self.config.url.clone())
                    .build()?;
                provider.parameters(model).await
            }
        }
    }
}
