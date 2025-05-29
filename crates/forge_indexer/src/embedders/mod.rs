mod openai;

pub use openai::*;

pub struct EmbedderInput<T> {
    pub payload: T,
}

pub struct EmbedderOutput {
    pub embeddings: Vec<f32>,
}

/// Embedder trait for embedding documents
#[async_trait::async_trait]
pub trait Embedder: Send + Sync {
    async fn embed<T, In>(
        &self,
        inputs: Vec<EmbedderInput<T>>,
    ) -> anyhow::Result<Vec<EmbedderOutput>>
    where
        T: ToString + Send,
        In: Into<EmbedderInput<T>> + Send;
}
