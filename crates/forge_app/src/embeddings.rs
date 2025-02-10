use std::path::PathBuf;

use anyhow::Result;
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};
use forge_domain::Embedding;

pub struct Embedder {
    options: InitOptions,
}

impl Default for Embedder {
    fn default() -> Self {
        let options =
            InitOptions::new(EmbeddingModel::AllMiniLML6V2).with_show_download_progress(true);
        Self { options }
    }
}

impl Embedder {
    pub fn new(cache_dir: PathBuf) -> Self {
        let init_options = InitOptions::new(EmbeddingModel::AllMiniLML6V2)
            .with_show_download_progress(true)
            .with_cache_dir(cache_dir);

        Self { options: init_options }
    }
}

impl Embedder {
    pub fn embed(&self, text: String) -> Result<Embedding> {
        let embeddings = TextEmbedding::try_new(self.options.clone())?.embed(vec![text], None)?;
        embeddings
            .into_iter()
            .next()
            .map(Embedding::new)
            .ok_or_else(|| anyhow::anyhow!("No embedding was generated"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_embedding() {
        let embedding = Embedder::default()
            .embed("Hello, world!".to_string())
            .unwrap();
        assert_eq!(embedding.as_slice().len(), 384);
    }
}
