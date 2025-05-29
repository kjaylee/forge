use std::path::Path;
use std::sync::Arc;

use crate::{Store, chunkers::Chunker, embedders::Embedder, loaders::Loader};

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

impl<
    Input,
    L: Loader<Output = Input>,
    C: Chunker<Input = L::Output>,
    E: Embedder<Input = C::Output>,
    S: Store<Input = E::Output>,
> Indexer<L, C, E, S>
{
    /// Indexes the files at the given path
    pub async fn index(&self, path: &Path) -> anyhow::Result<()> {
        self.store
            .store(
                self.embedder
                    .embed(self.chunker
                        .chunk(self.loader
                            .load(path).await?).await?)
                    .await?,
            )
            .await?;
        Ok(())
    }
}