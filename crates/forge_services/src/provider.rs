use std::future::Future;
use std::sync::Arc;

use anyhow::Result;
use forge_domain::{
    ChatCompletionMessage, Context as ChatContext, Model, ModelId, ResultStream, RetryConfig,
};
use forge_provider::Client;

use crate::services::{EnvironmentService, ProviderService};
use crate::Infrastructure;

#[derive(Clone)]
pub struct ForgeProviderService {
    // The provider service implementation
    client: Arc<Client>,
    retry_config: RetryConfig,
}

impl ForgeProviderService {
    pub fn new<F: Infrastructure>(infra: Arc<F>) -> Self {
        let infra = infra.clone();
        let env = infra.environment_service().get_environment();
        let provider = env.provider.clone();
        let retry_config = env.retry_config.clone();
        let version = env.version();
        Self {
            client: Arc::new(Client::new(provider, retry_config.clone(), version).unwrap()),
            retry_config,
        }
    }

    /// Retry wrapper for models API operations that may fail with retryable
    /// errors
    async fn attempt_models_retry<T, FutureFn, Fut>(&self, f: FutureFn) -> Result<T>
    where
        FutureFn: FnMut() -> Fut,
        Fut: Future<Output = anyhow::Result<T>>,
    {
        self.retry_config.retry(f).await
    }
}

#[async_trait::async_trait]
impl ProviderService for ForgeProviderService {
    async fn chat(
        &self,
        model: &ModelId,
        request: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        self.client.chat(model, request).await
    }

    async fn models(&self) -> Result<Vec<Model>> {
        self.attempt_models_retry(|| self.client.models()).await
    }
}
