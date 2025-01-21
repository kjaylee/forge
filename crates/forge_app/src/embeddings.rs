use anyhow::Result;
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};
use forge_domain::Embedding;

pub struct Embedder;

impl Embedder {
    // TODO: Specify the central cache folder path; otherwise, the cache directory
    // will default to the current working directory of the binary.
    pub fn embed(text: String) -> Result<Embedding> {
        let model = TextEmbedding::try_new(
            InitOptions::new(EmbeddingModel::AllMiniLML6V2).with_show_download_progress(true),
        )?;
        let embeddings = model.embed(vec![text], None)?;
        embeddings
            .into_iter()
            .next()
            .map(|e| Embedding::new(e))
            .ok_or_else(|| anyhow::anyhow!("No embedding was generated"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_embedding() {
        let embedding = Embedder::embed("Hello, world!".to_string()).unwrap();
        assert_eq!(embedding.as_slice().len(), 384);
    }
}
