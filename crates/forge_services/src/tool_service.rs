use std::collections::HashMap;
use std::sync::Arc;

use forge_domain::{
    Tool, ToolCallContext, ToolCallFull, ToolDefinition, ToolName, ToolResult, ToolService,
};
use tokio::time::{timeout, Duration};
use tracing::{debug, error};

use crate::tools::ToolRegistry;
use crate::Infrastructure;

// Timeout duration for tool calls
const TOOL_CALL_TIMEOUT: Duration = Duration::from_secs(300);

#[derive(Clone)]
pub struct ForgeToolService {
    tools: Arc<HashMap<ToolName, Tool>>,
}

impl ForgeToolService {
    pub fn new<F: Infrastructure>(infra: Arc<F>) -> Self {
        let registry = ToolRegistry::new(infra.clone());
        ForgeToolService::from_iter(registry.tools())
    }
}

impl FromIterator<Tool> for ForgeToolService {
    fn from_iter<T: IntoIterator<Item = Tool>>(iter: T) -> Self {
        let tools: HashMap<ToolName, Tool> = iter
            .into_iter()
            .map(|tool| (tool.definition.name.clone(), tool))
            .collect::<HashMap<_, _>>();

        Self { tools: Arc::new(tools) }
    }
}

#[async_trait::async_trait]
impl ToolService for ForgeToolService {
    async fn call(&self, context: ToolCallContext, call: ToolCallFull) -> ToolResult {
        let name = call.name.clone();
        let input = call.arguments.clone();
        debug!(tool_name = ?call.name, arguments = ?call.arguments, "Executing tool call");
        // Get agent and conversation from context
        let available_tools = {
            if let (Some(conversation), Some(agent)) =
                (context.conversation.as_ref(), context.agent.as_ref())
            {
                conversation
                    .get_allowed_tools(&agent.id)
                    .unwrap_or_default()
            } else {
                Vec::new()
            }
        };

        let output =
            match self.tools.get(&name) {
                Some(tool) => {
                    // Wrap tool call with timeout
                    match timeout(TOOL_CALL_TIMEOUT, tool.executable.call(context, input)).await {
                        Ok(result) => result,
                        Err(_) => Err(anyhow::anyhow!(
                            "Tool '{}' timed out after {} minutes",
                            name.as_str(),
                            TOOL_CALL_TIMEOUT.as_secs() / 60
                        )),
                    }
                }
                None => {
                    Err(anyhow::anyhow!(
                "No tool with name '{}' was found. Please try again with one of these tools {}",
                name.as_str(),
                available_tools.iter().map(|s| s.as_str()).collect::<Vec<&str>>().join(", ")
            ))
                }
            };

        let result = match output {
            Ok(output) => ToolResult::from(call).success(output),
            Err(output) => {
                error!(error = ?output, "Tool call failed");
                ToolResult::from(call).failure(output)
            }
        };

        debug!(result = ?result, "Tool call result");
        result
    }

    fn list(&self) -> Vec<ToolDefinition> {
        let mut tools: Vec<_> = self
            .tools
            .values()
            .map(|tool| tool.definition.clone())
            .collect();

        // Sorting is required to ensure system prompts are exactly the same
        tools.sort_by(|a, b| a.name.as_str().cmp(b.name.as_str()));

        tools
    }

    fn usage_prompt(&self, agent: &forge_domain::Agent, mode: forge_domain::Mode) -> String {
        // Get mode-specific tools from the agent
        let agent_mode_tools = agent
            .modes
            .get(&mode)
            .and_then(|mode_config| mode_config.tools.as_ref());

        // Get general tools from the agent
        let agent_general_tools = agent.tools.as_ref();

        // Legacy mode-specific tools (act_tools and plan_tools) have been removed

        // Filter tools based on the current mode
        let mut tools: Vec<_> = self
            .tools
            .values()
            .filter(|tool| {
                let tool_name = &tool.definition.name;

                // Check if the tool is in the agent's mode-specific tools
                if let Some(mode_tools) = agent_mode_tools {
                    if mode_tools.contains(tool_name) {
                        return true;
                    }
                }

                // Check if the tool is in the agent's general tools
                if let Some(general_tools) = agent_general_tools {
                    if general_tools.contains(tool_name) {
                        return true;
                    }
                }

                // Legacy mode-specific tools (act_tools and plan_tools) have been removed

                false
            })
            .collect();

        tools.sort_by(|a, b| a.definition.name.as_str().cmp(b.definition.name.as_str()));

        tools
            .iter()
            .enumerate()
            .fold("".to_string(), |mut acc, (i, tool)| {
                acc.push('\n');
                acc.push_str((i + 1).to_string().as_str());
                acc.push_str(". ");
                acc.push_str(tool.definition.usage_prompt().to_string().as_str());
                acc
            })
    }
}

#[cfg(test)]
mod test {
    use anyhow::bail;
    use forge_domain::{Tool, ToolCallContext, ToolCallId, ToolDefinition};
    use serde_json::{json, Value};
    use tokio::time;

    use super::*;

    // Mock tool that always succeeds
    struct SuccessTool;
    #[async_trait::async_trait]
    impl forge_domain::ExecutableTool for SuccessTool {
        type Input = Value;

        async fn call(
            &self,
            _context: ToolCallContext,
            input: Self::Input,
        ) -> anyhow::Result<String> {
            Ok(format!("Success with input: {}", input))
        }
    }

    // Mock tool that always fails
    struct FailureTool;
    #[async_trait::async_trait]
    impl forge_domain::ExecutableTool for FailureTool {
        type Input = Value;

        async fn call(
            &self,
            _context: ToolCallContext,
            _input: Self::Input,
        ) -> anyhow::Result<String> {
            bail!("Tool call failed with simulated failure".to_string())
        }
    }

    fn new_tool_service() -> impl ToolService {
        let success_tool = Tool {
            definition: ToolDefinition {
                name: ToolName::new("success_tool"),
                description: "A test tool that always succeeds".to_string(),
                input_schema: schemars::schema_for!(serde_json::Value),
                output_schema: Some(schemars::schema_for!(String)),
            },
            executable: Box::new(SuccessTool),
        };

        let failure_tool = Tool {
            definition: ToolDefinition {
                name: ToolName::new("failure_tool"),
                description: "A test tool that always fails".to_string(),
                input_schema: schemars::schema_for!(serde_json::Value),
                output_schema: Some(schemars::schema_for!(String)),
            },
            executable: Box::new(FailureTool),
        };

        ForgeToolService::from_iter(vec![success_tool, failure_tool])
    }

    #[tokio::test]
    async fn test_successful_tool_call() {
        let service = new_tool_service();
        let call = ToolCallFull {
            name: ToolName::new("success_tool"),
            arguments: json!("test input"),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(ToolCallContext::default(), call).await;
        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_failed_tool_call() {
        let service = new_tool_service();
        let call = ToolCallFull {
            name: ToolName::new("failure_tool"),
            arguments: json!("test input"),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(ToolCallContext::default(), call).await;
        insta::assert_snapshot!(result);
    }

    #[tokio::test]
    async fn test_tool_not_found() {
        let service = new_tool_service();
        let call = ToolCallFull {
            name: ToolName::new("nonexistent_tool"),
            arguments: json!("test input"),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(ToolCallContext::default(), call).await;
        insta::assert_snapshot!(result);
    }

    // Mock tool that simulates a long-running task
    struct SlowTool;
    #[async_trait::async_trait]
    impl forge_domain::ExecutableTool for SlowTool {
        type Input = Value;

        async fn call(
            &self,
            _context: ToolCallContext,
            _input: Self::Input,
        ) -> anyhow::Result<String> {
            // Simulate a long-running task that exceeds the timeout
            tokio::time::sleep(Duration::from_secs(400)).await;
            Ok("Slow tool completed".to_string())
        }
    }

    #[tokio::test(flavor = "current_thread")]
    async fn test_tool_timeout() {
        test::time::pause();

        let slow_tool = Tool {
            definition: ToolDefinition {
                name: ToolName::new("slow_tool"),
                description: "A test tool that takes too long".to_string(),
                input_schema: schemars::schema_for!(serde_json::Value),
                output_schema: Some(schemars::schema_for!(String)),
            },
            executable: Box::new(SlowTool),
        };

        let service = ForgeToolService::from_iter(vec![slow_tool]);
        let call = ToolCallFull {
            name: ToolName::new("slow_tool"),
            arguments: json!("test input"),
            call_id: Some(ToolCallId::new("test")),
        };

        // Advance time to trigger timeout
        test::time::advance(Duration::from_secs(305)).await;

        let result = service.call(ToolCallContext::default(), call).await;

        // Assert that the result contains a timeout error message
        let content_str = &result.content;
        assert!(
            content_str.contains("timed out"),
            "Expected timeout error message"
        );
        assert!(result.is_error, "Expected error result for timeout");
    }
}
