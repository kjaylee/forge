mod code_chunker;

pub use code_chunker::*;

/// Chunker trait for splitting documents into chunks
#[async_trait::async_trait]
pub trait Chunker: Send + Sync {
    type Input;
    type Output;
    async fn chunk(&self, input: Self::Input) -> anyhow::Result<Self::Output>;
}
