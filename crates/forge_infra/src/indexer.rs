use std::path::Path;
use std::sync::Arc;

use forge_indexer::{FileLoader, HnswStore, OpenAI, Orchestrator, QueryOptions, TreeSitterChunker};
use forge_services::IndexerService;
use serde::de::DeserializeOwned;

#[derive(Default, Clone)]
pub struct Indexer(
    Arc<Orchestrator<FileLoader, TreeSitterChunker<'static>, OpenAI, HnswStore<'static>>>,
);

#[async_trait::async_trait]
impl IndexerService for Indexer {
    async fn index(&self, path: &Path) -> anyhow::Result<()> {
        self.0.index(path).await
    }

    async fn query<V: DeserializeOwned + Send + Sync>(
        &self,
        query: &str,
    ) -> anyhow::Result<Vec<V>> {
        // TODO: allow caller to set query options.
        let results = self
            .0
            .query::<V>(query, QueryOptions::default().limit(10 as u64))
            .await?;
        Ok(results.into_iter().map(|output| output.payload).collect())
    }
}
