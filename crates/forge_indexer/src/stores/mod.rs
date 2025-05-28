mod qdrant;

pub use qdrant::*;

/// Store trait for storing embeddings
#[async_trait::async_trait]
pub trait Store: Send + Sync {
    type Input;
    async fn store(&self, embeddings: Self::Input) -> anyhow::Result<()>;
}
