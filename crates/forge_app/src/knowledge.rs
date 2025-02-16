use std::sync::Arc;

use forge_domain::{Knowledge, KnowledgeService, Query};
use rust_bert::pipelines::sentence_embeddings::{
    SentenceEmbeddingsBuilder, SentenceEmbeddingsModel, SentenceEmbeddingsModelType,
};
use serde_json::Value;

use crate::{InformationRepository, Infrastructure};

pub struct TextualKnowledgeService<F> {
    infra: Arc<F>,
}
impl<F> TextualKnowledgeService<F> {
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
impl<F: Infrastructure> KnowledgeService<String> for TextualKnowledgeService<F> {
    async fn search(&self, query: Query) -> anyhow::Result<Vec<Knowledge<String>>> {
        let embedding = self.encode(&query.input)?;
        let results = self
            .infra
            .textual_knowledge_repo()
            .search(embedding)
            .await?;
        Ok(results
            .into_iter()
            .map(|k| Ok(k.try_map(|v| serde_json::to_string(&v))?))
            .collect::<anyhow::Result<Vec<_>>>()?)
    }

    async fn store(&self, content: Vec<String>) -> anyhow::Result<()> {
        let knows = content
            .into_iter()
            .map(|content| {
                let embedding = self.encode(content.as_str())?;
                Ok(Knowledge::new(Value::from(content), embedding))
            })
            .collect::<anyhow::Result<Vec<_>>>()?;

        self.infra.textual_knowledge_repo().upsert(knows).await?;

        Ok(())
    }

    async fn list(&self) -> anyhow::Result<Vec<Knowledge<String>>> {
        self.infra
            .textual_knowledge_repo()
            .list()
            .await?
            .into_iter()
            .map(|k| Ok(k.try_map(|v| serde_json::to_string(&v))?))
            .collect::<anyhow::Result<Vec<_>>>()
    }
}
