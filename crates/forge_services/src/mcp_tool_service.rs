use forge_domain::{ToolCallContext, ToolCallFull, ToolDefinition, ToolResult, ToolService};

pub struct McpToolService {}

#[async_trait::async_trait]
impl ToolService for McpToolService {
    async fn call(&self, _: ToolCallContext, _: ToolCallFull) -> ToolResult {
        todo!()
    }
    fn list(&self) -> Vec<ToolDefinition> {
        todo!()
    }
}
