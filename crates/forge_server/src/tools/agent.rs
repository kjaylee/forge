use std::collections::HashMap;
use std::sync::Arc;

use forge_domain::{
    ChatRequest, ChatResponse, Context, ModelId, TemplateVars, ToolCallService, ToolDescription,
};
use schemars::JsonSchema;
use serde::Deserialize;
use tokio_stream::StreamExt;

use crate::service::ChatService;
use crate::Error;

pub struct AgentTool {
    chat_svc: Arc<dyn ChatService>,
    desc: String,
}

impl AgentTool {
    pub fn new(chat_svc: Arc<dyn ChatService>, desc: impl ToString) -> Self {
        Self { chat_svc, desc: desc.to_string() }
    }
}

impl ToolDescription for AgentTool {
    fn description(&self) -> String {
        self.desc.clone()
    }
}

#[derive(Deserialize, JsonSchema)]
pub struct AgentInput {
    pub request: String,
    pub vars: Option<HashMap<String, String>>,
}

impl From<AgentInput> for ChatRequest {
    fn from(input: AgentInput) -> Self {
        ChatRequest::new(input.request)
            .model(ModelId::new("anthropic/claude-3.5-sonnet"))
            .template_vars(TemplateVars::from(input.vars.unwrap_or_default()))
    }
}

#[async_trait::async_trait]
impl ToolCallService for AgentTool {
    type Input = AgentInput;
    type Output = String;
    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        // TODO: take the model as input to either in AgentInput or in the constructor.
        let stream = self
            .chat_svc
            .chat(input.into(), Context::default())
            .await
            .map_err(|e| e.to_string())?;

        let text_output: Vec<String> = stream
            .filter_map(|response: Result<ChatResponse, Error>| {
                if let Ok(ChatResponse::Text(text)) = response {
                    Some(text)
                } else {
                    None
                }
            })
            .collect()
            .await;

        Ok(text_output.join(""))
    }
}
