use std::time::Duration;

use serde::de::DeserializeOwned;

use crate::{ToolCallFull, ToolDefinition, ToolResult};

#[async_trait::async_trait]
pub trait ToolCallService {
    type Input: DeserializeOwned;

    async fn call(&self, input: Self::Input) -> Result<String, String>;
}

#[async_trait::async_trait]
pub trait ToolService: Send + Sync {
    async fn call(&self, call: ToolCallFull) -> ToolResult;
    async fn set_timeout(&self, duration: Duration) -> anyhow::Result<()>;
    fn list(&self) -> Vec<ToolDefinition>;
    fn usage_prompt(&self) -> String;
}
