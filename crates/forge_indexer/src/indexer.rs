use std::path::Path;
use std::sync::Arc;

use crate::{
    EmbedderInput, Store, StoreInput, chunkers::Chunker, embedders::Embedder, loaders::Loader,
};

impl From<&forge_treesitter::Block> for EmbedderInput<String> {
    fn from(block: &forge_treesitter::Block) -> Self {
        let payload = serde_json::json!({
            "path": block.relative_path(),
            "code": block.snippet,
        })
        .to_string();

        Self { payload }
    }
}

/// Indexer for indexing files
pub struct Indexer<L: Loader, C: Chunker, E: Embedder, S: Store> {
    loader: Arc<L>,
    chunker: Arc<C>,
    embedder: Arc<E>,
    store: Arc<S>,
}

impl<L: Loader, C: Chunker, E: Embedder, S: Store> Indexer<L, C, E, S> {
    pub fn new(loader: Arc<L>, chunker: Arc<C>, embedder: Arc<E>, store: Arc<S>) -> Self {
        Self { loader, chunker, embedder, store }
    }
}

impl<L: Loader, C: Chunker, E: Embedder, S: Store> Indexer<L, C, E, S> {
    pub async fn index(&self, path: &Path) -> anyhow::Result<()> {
        let files = self.loader.load(path).await?;
        let code_blocks = self.chunker.chunk(files).await?;
        let embeddings = self
            .embedder
            .embed::<String, EmbedderInput<String>>(code_blocks.iter().map(Into::into).collect())
            .await?;

        self.store
            .store(
                code_blocks
                    .into_iter()
                    .zip(embeddings.into_iter())
                    .map(|(block, embeddings)| StoreInput {
                        embeddings: embeddings.embeddings,
                        metadata: serde_json::json!({
                            "path": block.relative_path(),
                            "kind": block.kind.to_string(),
                            "span": block.span,
                            "scope": block.scope.map(|s| s.to_string()),
                            "offset": block.offset,
                        }),
                    })
                    .collect(),
            )
            .await?;
        Ok(())
    }
}
