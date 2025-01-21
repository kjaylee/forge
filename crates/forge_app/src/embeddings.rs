use anyhow::Result;

 use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};

 pub fn get_embedding(text: String) -> Result<Vec<f32>> {
     let model = TextEmbedding::try_new(
         InitOptions::new(EmbeddingModel::AllMiniLML6V2).with_show_download_progress(true),
     )?;
     let embeddings = model.embed(vec![text], None)?;
     embeddings.into_iter().next().ok_or_else(|| anyhow::anyhow!("No embedding was generated"))
 }

 #[cfg(test)]
 mod tests {
     use super::*;

     #[test]
     fn test_get_embedding() {
         let embedding = get_embedding("Hello, world!".to_string()).unwrap();
         assert_eq!(embedding.len(), 384);
     }
 }