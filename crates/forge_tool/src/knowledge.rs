use std::sync::Arc;

use forge_domain::{
    App, ExecutableTool, KnowledgeService, NamedTool, Query, ToolDescription, ToolName,
};

pub struct RecallKnowledge<F> {
    app: Arc<F>,
}

impl<F> ToolDescription for RecallKnowledge<F> {
    fn description(&self) -> String {
        "Get knowledge from the app".to_string()
    }
}

#[derive(serde::Deserialize)]
pub struct GetKnowledgeInput {
    pub query: String,
}

#[async_trait::async_trait]
impl<F: App> ExecutableTool for RecallKnowledge<F> {
    type Input = GetKnowledgeInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        let learnings = self
            .app
            .information_service()
            .search(Query::default().input(input.query))
            .await
            .map_err(|e| e.to_string())?;

        Ok(learnings
            .into_iter()
            .map(|l| l.content)
            .collect::<Vec<_>>()
            .join("\n"))
    }
}

impl<F> NamedTool for RecallKnowledge<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_knowledge_get".to_string())
    }
}

pub struct StoreKnowledge<F: App> {
    app: Arc<F>,
}

impl<F: App> ToolDescription for StoreKnowledge<F> {
    fn description(&self) -> String {
        "Set knowledge to the app".to_string()
    }
}

#[derive(serde::Deserialize)]
pub struct SetKnowledgeInput {
    pub content: String,
}

#[async_trait::async_trait]
impl<F: App> ExecutableTool for StoreKnowledge<F> {
    type Input = SetKnowledgeInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        self.app
            .information_service()
            .store(&input.content)
            .await
            .map_err(|e| e.to_string())?;

        Ok("Knowledge stored successfully".to_string())
    }
}

impl<F: App> NamedTool for StoreKnowledge<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_knowledge_set".to_string())
    }
}
