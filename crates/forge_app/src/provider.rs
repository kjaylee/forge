use std::sync::Arc;

use anyhow::{Context, Result};
use forge_domain::{
    ChatCompletionMessage, Context as ChatContext, Model, ModelId, Parameters, Provider,
    ProviderService, ResultStream,
};
use forge_open_router::{Client, ClientBuilder};
use moka2::future::Cache;
use tokio::sync::Mutex;

use crate::{EnvironmentService, Infrastructure};

pub struct ForgeProviderService {
    // The provider service implementation
    client: Mutex<Option<Arc<Client>>>,
    cache: Cache<ModelId, Parameters>,
    provider: Provider,
}

impl ForgeProviderService {
    pub fn new<F: Infrastructure>(infra: Arc<F>) -> Self {
        let infra = infra.clone();
        let provider = infra
            .environment_service()
            .get_environment()
            .provider
            .clone();
        Self { client: Mutex::new(None), cache: Cache::new(1024), provider }
    }

    async fn client(&self) -> Result<Arc<Client>> {
        let mut guard = self.client.lock().await;
        if let Some(provider) = guard.as_ref() {
            return Ok(provider.clone());
        }

        let provider = Arc::new(ClientBuilder::new(self.provider.clone()).build()?);

        *guard = Some(provider.clone());
        Ok(provider)
    }
}

#[async_trait::async_trait]
impl ProviderService for ForgeProviderService {
    async fn chat(
        &self,
        model_id: &ModelId,
        request: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        self.client()
            .await?
            .chat(model_id, request)
            .await
            .with_context(|| format!("Failed to chat with model: {}", model_id))
    }

    async fn models(&self) -> Result<Vec<Model>> {
        self.client().await?.models().await
    }

    async fn parameters(&self, model: &ModelId) -> anyhow::Result<Parameters> {
        self.cache
            .try_get_with_by_ref(model, async {
                self.client()
                    .await?
                    .parameters(model)
                    .await
                    .with_context(|| format!("Failed to get parameters for model: {}", model))
            })
            .await
            .map_err(|e| anyhow::anyhow!(e))
    }
}
