mod qdrant;

pub use qdrant::*;

pub struct StoreInput<T> {
    pub embeddings: Vec<f32>,
    pub metadata: T,
}

/// Store trait for storing embeddings
#[async_trait::async_trait]
pub trait Store: Send + Sync {
    async fn store<T>(&self, inputs: Vec<StoreInput<T>>) -> anyhow::Result<()>
    where
        T: Into<serde_json::Value> + Send + Sync;
}
