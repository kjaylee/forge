mod openai;

pub use openai::*;

pub struct EmbedderInput<T> {
    pub payload: T,
}

impl<P: AsRef<str>> EmbedderInput<P> {
    fn hash(&self) -> String {
        use blake3::Hasher as Blake3;
        let mut hasher = Blake3::new();
        hasher.update(self.payload.as_ref().as_bytes());
        let hash = hasher.finalize();
        hash.to_hex().to_string()
    }
}

#[derive(Clone)]
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
