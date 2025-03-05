use std::sync::Arc;

use anyhow::{Context, Result};
use forge_domain::{
    AuthService, ChatCompletionMessage, Context as ChatContext, Model, ModelId, Parameters, ProviderService, ResultStream
};
use forge_open_router::ProviderBuilder;
use moka2::future::Cache;

use crate::{EnvironmentService, Infrastructure};

pub struct ForgeProviderService<F> {
    infra: Arc<F>,
    or: Option<Arc<dyn ProviderService>>,
    cache: Cache<ModelId, Parameters>,
}

impl <F: Infrastructure> ForgeProviderService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        let infra = infra.clone();
        Self { infra, or: None,cache: Cache::new(1024) }
    }

    fn with_provider_service(&self, provider: Arc<dyn ProviderService>) -> Self {
        Self { infra: self.infra.clone(), or: Some(provider), cache: self.cache.clone() }
    }

    pub fn build_provider_service(&self) -> Result<Self> {
        if let Some(_) = self.or {
            return Ok(Self{
                infra: self.infra.clone(),
                or: self.or.clone(),
                cache: self.cache.clone()
            });
        }
        let env = self.infra.environment_service().get_environment();
        let key = if let Some(_antinomy) = env.force_antinomy {
            self.infra.auth_service().get_auth_token().ok_or_else(|| anyhow::anyhow!("No auth token found run login command to login"))?
        } else {
            env.provider_key.clone()
        };
        let or = ProviderBuilder::from_url(env.provider_url)
            .with_key(key)
            .build()?;
        Ok(self.with_provider_service(or))
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ProviderService for ForgeProviderService<F> {
    async fn chat(
        &self,
        model_id: &ModelId,
        request: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        let this: ForgeProviderService<F> = self.build_provider_service()?;
        this.or.as_ref().ok_or_else(|| anyhow::anyhow!("Provider service not initialized"))?
            .chat(model_id, request)
            .await
            .with_context(|| format!("Failed to chat with model: {}", model_id))
    }

    async fn models(&self) -> Result<Vec<Model>> {
        let this = self.build_provider_service()?;
        this.or.as_ref().ok_or_else(|| anyhow::anyhow!("Provider service not initialized"))?.models().await
    }

    async fn parameters(&self, model: &ModelId) -> anyhow::Result<Parameters> {
        let this = self.build_provider_service()?;
        Ok(this
            .cache
            .try_get_with_by_ref(model, async {
                this.or.as_ref().ok_or_else(|| anyhow::anyhow!("Provider service not initialized"))?
                    .parameters(model)
                    .await
                    .with_context(|| format!("Failed to get parameters for model: {}", model))
            })
            .await
            .map_err(|e| anyhow::anyhow!(e))?)
    }
}
