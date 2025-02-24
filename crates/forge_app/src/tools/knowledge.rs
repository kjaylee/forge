use std::sync::Arc;

use forge_domain::{ExecutableTool, NamedTool, Query, ToolDescription, ToolName};
use schemars::JsonSchema;

use crate::{EmbeddingService, Infrastructure, VectorIndex};

pub struct RecallKnowledge<F> {
    infra: Arc<F>,
}

impl<F> ToolDescription for RecallKnowledge<F> {
    fn description(&self) -> String {
        "Get knowledge from the app".to_string()
    }
}

impl<F> RecallKnowledge<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self { infra }
    }
}

#[derive(serde::Deserialize, JsonSchema)]
pub struct GetKnowledgeInput {
    pub query: String,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for RecallKnowledge<F> {
    type Input = GetKnowledgeInput;

    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        let embedding = self.infra.embedding_service().embed(&input.query).await?;
        let out = self
            .infra
            .vector_index()
            .search(Query::new(embedding))
            .await?
            .into_iter()
            .map(|k| serde_json::to_string(&k))
            .collect::<Result<Vec<_>, _>>()?
            .join("\n");

        Ok(out)
    }
}

impl<F> NamedTool for RecallKnowledge<F> {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_knowledge_get".to_string())
    }
}
