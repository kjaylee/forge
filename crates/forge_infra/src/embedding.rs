use forge_app::EmbeddingService;
use fastembed::{EmbeddingModel, InitOptions, TextEmbedding};

pub struct ForgeEmbeddingService {}

impl Default for ForgeEmbeddingService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeEmbeddingService {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl EmbeddingService for ForgeEmbeddingService {
    async fn embed(&self, sentence: &str) -> anyhow::Result<Vec<f32>> {
        let model = TextEmbedding::try_new(
            InitOptions::new(EmbeddingModel::AllMiniLML6V2).with_show_download_progress(true),
        )?;
        
        Ok(model.embed(vec![sentence], None)?.concat())
    }
}
