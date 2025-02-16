use forge_app::EmbeddingService;

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
    async fn embed(&self, _text: &str) -> anyhow::Result<Vec<f32>> {
        unimplemented!()
    }
}
