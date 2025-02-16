use std::sync::Arc;

use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};

use crate::Infrastructure;

pub struct RecallKnowledge<F> {
    infra: Arc<F>,
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
impl<F: Infrastructure> ExecutableTool for RecallKnowledge<F> {
    type Input = GetKnowledgeInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        todo!()
    }
}

impl<F> NamedTool for RecallKnowledge<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_knowledge_get".to_string())
    }
}

pub struct StoreKnowledge<F> {
    infra: Arc<F>,
}

impl<F> ToolDescription for StoreKnowledge<F> {
    fn description(&self) -> String {
        "Set knowledge to the app".to_string()
    }
}

#[derive(serde::Deserialize)]
pub struct StoreKnowledgeInput {
    pub content: String,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for StoreKnowledge<F> {
    type Input = StoreKnowledgeInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        todo!()
    }
}

impl<F> NamedTool for StoreKnowledge<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_knowledge_set".to_string())
    }
}
