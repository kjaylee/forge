use std::result::Result;
use std::sync::Arc;

use forge_domain::{
    ChatCompletionMessage, Context as ChatContext, EnvironmentService, Model, ModelId,
    ProviderService, ResultStream,
};
use forge_provider::Client;

use crate::Infrastructure;

#[derive(Clone)]
pub struct ForgeProviderService<P: ProviderService> {
    // The provider service implementation
    client: Arc<P>,
}

impl ForgeProviderService<Client> {
    pub fn new<F: Infrastructure>(infra: Arc<F>) -> Self {
        let infra = infra.clone();
        let env = infra.environment_service().get_environment();
        let provider = env.provider.clone();
        Self { client: Arc::new(Client::new(provider).unwrap()) }
    }
}

#[async_trait::async_trait]
impl<P: ProviderService> ProviderService for ForgeProviderService<P> {
    type Error = P::Error;
    async fn chat(
        &self,
        model: &ModelId,
        request: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, Self::Error> {
        self.client.chat(model, request).await
    }

    async fn models(&self) -> Result<Vec<Model>, Self::Error> {
        self.client.models().await
    }
}
