use std::path::PathBuf;

use anyhow::Result;
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};
use forge_domain::Embedding;

pub struct Embedder {
    options: InitOptions,
}

impl Default for Embedder {
    fn default() -> Self {
        Self { options: Self::init_options(None) }
    }
}

impl Embedder {
    pub fn new(cache_dir: PathBuf) -> Self {
        Self { options: Self::init_options(Some(cache_dir)) }
    }

    // Private method to create InitOptions
    fn init_options(cache_dir: Option<PathBuf>) -> InitOptions {
        let mut init_options =
            InitOptions::new(EmbeddingModel::AllMiniLML6V2).with_show_download_progress(true);

        if let Some(cache_dir) = cache_dir {
            init_options = init_options.with_cache_dir(cache_dir);
        }

        #[cfg(test)]
        {
            // in case of tests, instead of referring to temp dir and always downloading the model info
            // refer to the actual cache dir where this information is stored.
            use crate::EnvironmentFactory;
            let cache_dir = EnvironmentFactory::new(".".into(), false)
                .create()
                .unwrap()
                .cache_dir();
            init_options = init_options.with_cache_dir(cache_dir);
        }

        init_options
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
