use anyhow::Result;

use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};

pub fn get_embedding(text: String) -> Result<Vec<f32>> {
    let model = TextEmbedding::try_new(
        InitOptions::new(EmbeddingModel::AllMiniLML6V2).with_show_download_progress(true),
    )?;
    let embeddings = model.embed(vec![text], None)?;
    Ok(embeddings[0].clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_get_embedding() {
        let embedding = get_embedding("Hello, world!".to_string()).unwrap();
        assert_eq!(embedding.len(), 384);
    }
}
