mod chunkers;
mod embedders;
mod orchestrator;
mod loaders;
mod stores;
mod token_counter;

pub use chunkers::*;
pub use embedders::*;
pub use orchestrator::*;
pub use loaders::*;
pub use stores::*;
pub use token_counter::*;

#[cfg(test)]
mod tests {
    use crate::{FileLoader, Orchestrator, OpenAI, QdrantStore, TreeSitterChunker};
    use std::path::Path;
    use std::sync::Arc;

    #[tokio::test]
    async fn test_indexer() {
        dotenv::dotenv().ok();

        let embedding_model = "text-embedding-3-large";
        let loader = FileLoader::default().with_extensions(vec!["rs".to_string()]);
        let chunker = TreeSitterChunker::new(embedding_model, 8192);
        let embedder = OpenAI::new(embedding_model, 1536);
        let store = QdrantStore::try_new(
            "https://c55da98e-e560-48d0-afb0-5a2f9d7456a6.europe-west3-0.gcp.cloud.qdrant.io:6334",
            "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJhY2Nlc3MiOiJtIn0.8M8EzfjVo9LkDMqgR_L6uVUaTV7Y45he68m7uqD1lrs",
            "testing",
        )
        .unwrap();

        let indexer: Orchestrator<FileLoader, TreeSitterChunker, OpenAI, QdrantStore> = Orchestrator::new(
            Arc::new(loader),
            Arc::new(chunker),
            Arc::new(embedder),
            Arc::new(store),
        );
        let _ = indexer.index(Path::new("/Users/ranjit/Desktop/workspace/code-forge/code-forge/crates/forge_main/src/prompt.rs")).await.unwrap();
    }
}
