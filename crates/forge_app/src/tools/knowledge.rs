use std::sync::Arc;

use forge_domain::{ExecutableTool, Knowledge, NamedTool, Query, ToolDescription, ToolName};
use schemars::JsonSchema;
use serde_json::json;

use crate::{EmbeddingService, Infrastructure, KnowledgeRepository};

pub struct RecallKnowledge<F, R> {
    infra: Arc<F>,
    embed: Arc<R>,
}

impl<F, R> ToolDescription for RecallKnowledge<F, R> {
    fn description(&self) -> String {
        "Get knowledge from the app".to_string()
    }
}

impl<F, R> RecallKnowledge<F, R> {
    pub fn new(infra: Arc<F>, embed: Arc<R>) -> Self {
        Self { infra, embed }
    }
}

#[derive(serde::Deserialize, JsonSchema)]
pub struct GetKnowledgeInput {
    pub query: String,
}

#[async_trait::async_trait]
impl<F: Infrastructure, R: EmbeddingService> ExecutableTool for RecallKnowledge<F, R> {
    type Input = GetKnowledgeInput;

    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        let embedding = self.embed.encode(&input.query).await?;
        let out = self
            .infra
            .textual_knowledge_repo()
            .search(Query::new(embedding))
            .await?
            .into_iter()
            .map(|k| serde_json::to_string(&k))
            .collect::<Result<Vec<_>, _>>()?
            .join("\n");

        Ok(out)
    }
}

impl<F, R> NamedTool for RecallKnowledge<F, R> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_knowledge_get".to_string())
    }
}

pub struct StoreKnowledge<F, R> {
    infra: Arc<F>,
    embed: Arc<R>,
}

impl<F, R> StoreKnowledge<F, R> {
    pub fn new(infra: Arc<F>, embed: Arc<R>) -> Self {
        Self { infra, embed }
    }
}

impl<F, R> ToolDescription for StoreKnowledge<F, R> {
    fn description(&self) -> String {
        "Set knowledge to the app".to_string()
    }
}

#[derive(serde::Deserialize, JsonSchema)]
pub struct StoreKnowledgeInput {
    pub content: String,
}

#[async_trait::async_trait]
impl<F: Infrastructure, R: EmbeddingService> ExecutableTool for StoreKnowledge<F, R> {
    type Input = StoreKnowledgeInput;

    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        let embedding = self.embed.encode(&input.content).await?;
        let knowledge = Knowledge::new(json!({"content": input.content}), embedding);
        self.infra
            .textual_knowledge_repo()
            .store(vec![knowledge])
            .await?;

        Ok("Updated knowledge successfully".to_string())
    }
}

impl<F, R> NamedTool for StoreKnowledge<F, R> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_knowledge_set".to_string())
    }
}
