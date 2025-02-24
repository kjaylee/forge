use async_openai::config::OpenAIConfig;
use async_openai::types::{CreateEmbeddingRequestArgs, EmbeddingInput};
use async_openai::Client;
use forge_app::EmbeddingService;

pub struct ForgeEmbeddingService {
    client: Client<OpenAIConfig>,
}

impl Default for ForgeEmbeddingService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeEmbeddingService {
    pub fn new() -> Self {
        Self { client: Client::with_config(OpenAIConfig::default()) }
    }
}

#[async_trait::async_trait]
impl EmbeddingService for ForgeEmbeddingService {
    async fn embed(&self, sentence: &str) -> anyhow::Result<Vec<f32>> {
        let request = CreateEmbeddingRequestArgs::default()
            .model("text-embedding-ada-002")
            .input(EmbeddingInput::String(sentence.to_string()))
            .build()?;

        let response = self.client.embeddings().create(request).await?;
        let out = response
            .data
            .iter()
            .map(|embedding| embedding.embedding.clone())
            .collect::<Vec<_>>();
        Ok(out.concat())
    }
}
