use std::sync::Arc;

use anyhow::{Context, Result};
use backon::{ExponentialBuilder, Retryable};
use forge_domain::{
    ChatCompletionMessage, Context as ChatContext, Error, Model, ModelId, ResultStream, RetryConfig,
};
use forge_provider::Client;
use tracing::warn;

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
}

#[async_trait::async_trait]
impl ProviderService for ForgeProviderService {
    async fn chat(
        &self,
        model: &ModelId,
        request: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        let retry_config = &self.retry_config;
        (|| self.client.chat(model, request.clone()))
            .retry(
                ExponentialBuilder::default()
                    .with_factor(retry_config.backoff_factor as f32)
                    .with_max_times(retry_config.max_retry_attempts)
                    .with_jitter(),
            )
            .when(should_retry)
            .await
            .with_context(|| format!("Failed to chat with model: {model}"))
    }

    async fn models(&self) -> Result<Vec<Model>> {
        self.client.models().await
    }

    async fn model(&self, model: &ModelId) -> Result<Option<Model>> {
        self.client.model(model).await
    }
}

fn should_retry(error: &anyhow::Error) -> bool {
    let retry = error
        .downcast_ref::<Error>()
        .is_some_and(|error| matches!(error, Error::Retryable(_, _)));

    warn!(error = %error, retry = retry, "Retrying on error");
    retry
}
