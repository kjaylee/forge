use std::sync::Arc;

use forge_domain::{Knowledge, KnowledgeService, Query};
use rust_bert::pipelines::sentence_embeddings::builder::Remote;
use rust_bert::pipelines::sentence_embeddings::{
    SentenceEmbeddingsBuilder, SentenceEmbeddingsModel, SentenceEmbeddingsModelType,
};

use crate::{Infrastructure, KnowledgeRepository};

pub struct ForgeKnowledgeService<F> {
    infra: Arc<F>,
}
impl<F> ForgeKnowledgeService<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }

    fn model(&self) -> anyhow::Result<SentenceEmbeddingsModel> {
        Ok(
            SentenceEmbeddingsBuilder::remote(SentenceEmbeddingsModelType::AllMiniLmL12V2)
                .create_model()?,
        )
    }

    fn encode(&self, content: &str) -> anyhow::Result<Vec<f32>> {
        Ok(self.model()?.encode(&[content])?.concat())
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> KnowledgeService for ForgeKnowledgeService<F> {
    async fn search(&self, query: Query) -> anyhow::Result<Vec<Knowledge>> {
        let embedding = self.encode(&query.input)?;
        self.infra.knowledge_repo().search(embedding).await
    }

    async fn store(&self, content: &str) -> anyhow::Result<()> {
        let embedding = self.encode(content)?;
        self.infra
            .knowledge_repo()
            .insert(content, &embedding)
            .await
    }

    async fn list(&self) -> anyhow::Result<Vec<Knowledge>> {
        self.infra.knowledge_repo().list().await
    }
}
