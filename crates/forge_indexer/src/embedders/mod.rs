mod openai;

pub use openai::*;

/// Embedder trait for embedding documents
#[async_trait::async_trait]
pub trait Embedder: Send + Sync {
    type Output;
    type Input;
    async fn embed(&self, text: Self::Input) -> anyhow::Result<Self::Output>;
}
