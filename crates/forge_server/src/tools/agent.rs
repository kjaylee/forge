use std::sync::Arc;

use forge_domain::{ChatRequest, ChatResponse, Context, ModelId, ToolCallService, ToolDescription};
use futures::future::join_all;
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
}

#[async_trait::async_trait]
impl ToolCallService for AgentTool {
    type Input = Vec<AgentInput>;
    type Output = Vec<String>;
    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let futures = input.into_iter().map(|agent_input| async {
            let stream = self
                .chat_svc
                .chat(
                    ChatRequest::new(agent_input.request)
                        .model(ModelId::new("anthropic/claude-3.5-sonnet")),
                    Context::default(),
                )
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
        });
        let results = join_all(futures).await;
        results.into_iter().collect()
    }
}
