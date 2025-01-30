use std::pin::Pin;

use forge_domain::{ChatCompletionMessage, Context, ModelId};

pub type BoxStream<A, E> =
    Pin<Box<dyn tokio_stream::Stream<Item = std::result::Result<A, E>> + Send>>;

pub type ResultStream<A, E> = std::result::Result<BoxStream<A, E>, E>;

#[async_trait::async_trait]
pub trait ChatProvider: Send + Sync + 'static {
    async fn chat(
        &self,
        model_id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error>;
}

pub trait ForgeAPI: Send + Sync + 'static {
    type ChatProvider: ChatProvider;
    fn chat_provider(&self) -> &Self::ChatProvider;
}
