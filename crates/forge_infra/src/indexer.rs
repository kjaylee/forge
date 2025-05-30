use std::path::Path;
use std::sync::Arc;

use forge_indexer::{
    CachedEmbedder, FileLoader, HnswStore, OpenAI, Orchestrator, QueryOptions, TreeSitterChunker,
};
use forge_services::IndexerService;
use serde::de::DeserializeOwned;

#[derive(Default, Clone)]
pub struct Indexer(
    Arc<Orchestrator<FileLoader, TreeSitterChunker, CachedEmbedder<OpenAI>, HnswStore<'static>>>,
);

#[async_trait::async_trait]
impl IndexerService for Indexer {
    async fn index(&self, path: &Path) -> anyhow::Result<()> {
        self.0.index(path).await
    }

    async fn query<V: DeserializeOwned + Send + Sync>(
        &self,
        query: &str,
        options: forge_services::QueryOptions,
    ) -> anyhow::Result<Vec<V>> {
        let mut query_options = QueryOptions::default();
        query_options.limit = options.limit;

        if let Some(kind) = options.kind {
            query_options.kind = Some(kind);
        }
        if let Some(path) = options.path {
            query_options.path = Some(path);
        }
        let results = self.0.query::<V>(query, query_options).await?;
        Ok(results.into_iter().map(|output| output.payload).collect())
    }
}
