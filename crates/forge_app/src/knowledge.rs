use std::sync::Arc;

use forge_domain::{Knowledge, KnowledgeService, Query};
use rust_bert::pipelines::sentence_embeddings::{
    SentenceEmbeddingsBuilder, SentenceEmbeddingsModel, SentenceEmbeddingsModelType,
};
use serde_json::Value;

use crate::{Information, InformationId, InformationRepository, Infrastructure};

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
        self.infra.information_repo().search(embedding).await
    }

    async fn store(&self, content: &str) -> anyhow::Result<()> {
        let embedding = self.encode(content)?;
        let info = Information {
            id: InformationId::generate(),
            embedding,
            value: Value::from(content),
        };

        self.infra.information_repo().upsert(vec![info]).await?;

        Ok(())
    }

    async fn list(&self) -> anyhow::Result<Vec<Knowledge>> {
        self.infra.information_repo().list().await
    }
}
