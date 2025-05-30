mod chunkers;
mod embedders;
mod loaders;
mod orchestrator;
mod stores;
mod token_counter;

pub use chunkers::*;
pub use embedders::*;
pub use loaders::*;
pub use orchestrator::*;
pub use stores::*;
pub use token_counter::*;

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use crate::{CachedEmbedder, FileLoader, HnswStore, OpenAI, Orchestrator, TreeSitterChunker};

    #[tokio::test]
    async fn test_indexer() {
        dotenv::dotenv().ok();

        let embedding_model = "text-embedding-3-large";
        let embedding_dimensions = 1536;

        let cache_dir = format!(
            "{}:{}",
            embedding_model.replace("/", "-"),
            embedding_dimensions
        );
        let cache_path = std::env::current_dir()
            .expect("failed to retrive current working directory.")
            .join(PathBuf::from(format!("./cache/embeddings/{}", cache_dir)));

        let loader = FileLoader::default();
        let chunker = TreeSitterChunker::try_new(embedding_model, 8192).unwrap();
        let embedder = OpenAI::cached(&cache_path, embedding_model, embedding_dimensions).unwrap();
        let hnsw_store = HnswStore::new(embedding_dimensions as usize);

        let indexer: Orchestrator<
            FileLoader,
            TreeSitterChunker,
            CachedEmbedder<OpenAI>,
            HnswStore<'_>,
        > = Orchestrator::new(
            Arc::new(loader),
            Arc::new(chunker),
            Arc::new(embedder),
            Arc::new(hnsw_store),
        );
        let _ = indexer.index(Path::new("/Users/ranjit/Desktop/workspace/code-forge/code-forge/crates/forge_main/src/prompt.rs")).await.unwrap();
    }
}
