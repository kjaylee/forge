use std::sync::Arc;

use crate::Error;
use forge_domain::{ChatRequest, ChatResponse, Context, ToolCallService, ToolDescription};
use serde::Deserialize;
use tokio_stream::StreamExt;

use crate::service::ChatService;

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

#[derive(Deserialize)]
pub struct AgentInput {
    pub request: ChatRequest,
    pub context: Context,
}

#[async_trait::async_trait]
impl ToolCallService for AgentTool {
    type Input = AgentInput;
    type Output = String;
    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        // collect the answer as String.
        let stream = self
            .chat_svc
            .chat(input.request, input.context)
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
