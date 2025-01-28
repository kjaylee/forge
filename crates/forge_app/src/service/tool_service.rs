use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use forge_domain::{
    TokenCounter, Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult, ToolService,
};
use tokio::fs;
use tokio::time::{timeout, Duration};
use tracing::debug;
use uuid::Uuid;

use super::Service;

// Timeout duration for tool calls
const TOOL_CALL_TIMEOUT: Duration = Duration::from_secs(300);

/// Prefix for temporary files created by the system
pub const TEMP_FILE_PREFIX: &str = "forge_temp_";
impl Service {
    pub fn tool_service() -> impl ToolService {
        Live::from_iter(forge_tool::tools())
    }
}

struct TokenLimiter {
    token_counter: TokenCounter,
    temp_dir: PathBuf,
}

impl TokenLimiter {
    pub fn new() -> Self {
        Self {
            token_counter: TokenCounter::default(),
            temp_dir: std::env::temp_dir(),
        }
    }
    async fn create_temp_file(&self, content: String) -> Result<PathBuf, std::io::Error> {
        let temp_file = self
            .temp_dir
            .join(format!("{}_{}.txt", TEMP_FILE_PREFIX, Uuid::new_v4()));
        fs::write(&temp_file, content).await?;
        Ok(temp_file)
    }

    async fn process_output(&self, output: String) -> Result<String, String> {
        let token_count = self.token_counter.count_tokens(&output);
        if token_count > TokenCounter::MAX_TOOL_OUTPUT_TOKENS {
            let temp_file = self.create_temp_file(output).await;
            match temp_file {
                Ok(temp_file) => {
                    return Ok(format!(
                        "Output exceeds token limit ({} > {}). Written to temp file: {}, use search to find relevant information from this file",
                        token_count,
                        TokenCounter::MAX_TOOL_OUTPUT_TOKENS,
                        temp_file.display()
                    ));
                }
                Err(e) => {
                    return Err(format!(
                        "Output exceeds token limit ({} > {}). Failed to write output to temp file: {}.",
                        token_count,
                        TokenCounter::MAX_TOOL_OUTPUT_TOKENS,
                        e
                    ));
                }
            }
        }
        Ok(output)
    }
}

struct Live {
    tools: HashMap<ToolName, Tool>,
    limits: Arc<TokenLimiter>,
}

impl FromIterator<Tool> for Live {
    fn from_iter<T: IntoIterator<Item = Tool>>(iter: T) -> Self {
        let tools: HashMap<ToolName, Tool> = iter
            .into_iter()
            .map(|tool| (tool.definition.name.clone(), tool))
            .collect::<HashMap<_, _>>();
        let limits = Arc::new(TokenLimiter::new());
        Self { tools, limits }
    }
}

#[async_trait::async_trait]
impl ToolService for Live {
    async fn call(&self, call: ToolCallFull) -> ToolResult {
        let name = call.name.clone();
        let input = call.arguments.clone();
        debug!("Calling tool: {}", name.as_str());
        let mut available_tools = self
            .tools
            .keys()
            .map(|name| name.as_str())
            .collect::<Vec<_>>();

        available_tools.sort();
        let output = match self.tools.get(&name) {
            Some(tool) => {
                // Wrap tool call with timeout
                match timeout(TOOL_CALL_TIMEOUT, tool.executable.call(input)).await {
                    Ok(result) => result,
                    Err(_) => Err(format!(
                        "Tool '{}' timed out after {} minutes",
                        name.as_str(),
                        TOOL_CALL_TIMEOUT.as_secs() / 60
                    )),
                }
            }
            None => Err(format!(
                "No tool with name '{}' was found. Please try again with one of these tools {}",
                name.as_str(),
                available_tools.join(", ")
            )),
        };

        match output {
            Ok(output) => match self.limits.process_output(output).await {
                Ok(processed_output) => ToolResult::from(call).success(processed_output),
                Err(e) => ToolResult::from(call).failure(e),
            },
            Err(output) => match self.limits.process_output(output).await {
                Ok(processed_output) => ToolResult::from(call).failure(processed_output),
                Err(e) => ToolResult::from(call).failure(e),
            },
        }
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

    fn usage_prompt(&self) -> String {
        let mut tools: Vec<_> = self.tools.values().collect();
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
    use forge_domain::{Tool, ToolCallId, ToolDefinition};
    use serde_json::{json, Value};
    use tokio::time;

    use super::*;

    // Mock tool that always succeeds
    struct SuccessTool;
    #[async_trait::async_trait]
    impl forge_domain::ToolCallService for SuccessTool {
        type Input = Value;

        async fn call(&self, input: Self::Input) -> Result<String, String> {
            Ok(format!("Success with input: {}", input))
        }
    }

    // Mock tool that always fails
    struct FailureTool;
    #[async_trait::async_trait]
    impl forge_domain::ToolCallService for FailureTool {
        type Input = Value;

        async fn call(&self, _input: Self::Input) -> Result<String, String> {
            Err("Tool call failed with simulated failure".to_string())
        }
    }

    struct LongFailureTool;

    #[async_trait::async_trait]
    impl forge_domain::ToolCallService for LongFailureTool {
        type Input = Value;

        async fn call(&self, _input: Self::Input) -> Result<String, String> {
            let long_output = "all\n".repeat(TokenCounter::MAX_TOOL_OUTPUT_TOKENS + 1);
            Err(long_output)
        }
    }

    struct LongSuccessTool;

    #[async_trait::async_trait]
    impl forge_domain::ToolCallService for LongSuccessTool {
        type Input = Value;

        async fn call(&self, _input: Self::Input) -> Result<String, String> {
            let long_output = "all\n".repeat(TokenCounter::MAX_TOOL_OUTPUT_TOKENS + 1);
            Ok(long_output)
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

        let long_failure_tool = Tool {
            definition: ToolDefinition {
                name: ToolName::new("long_failure_tool"),
                description: "A test tool that fails with long output".to_string(),
                input_schema: schemars::schema_for!(serde_json::Value),
                output_schema: Some(schemars::schema_for!(String)),
            },
            executable: Box::new(LongFailureTool),
        };

        let long_success_tool = Tool {
            definition: ToolDefinition {
                name: ToolName::new("long_success_tool"),
                description: "A test tool that succeeds with long output".to_string(),
                input_schema: schemars::schema_for!(serde_json::Value),
                output_schema: Some(schemars::schema_for!(String)),
            },
            executable: Box::new(LongSuccessTool),
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

        Live::from_iter(vec![
            success_tool,
            failure_tool,
            long_failure_tool,
            long_success_tool,
        ])
    }

    #[tokio::test]
    async fn test_successful_tool_call() {
        let service = new_tool_service();
        let call = ToolCallFull {
            name: ToolName::new("success_tool"),
            arguments: json!("test input"),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
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

        let result = service.call(call).await;
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

        let result = service.call(call).await;
        insta::assert_snapshot!(result);
    }

    // Mock tool that simulates a long-running task
    struct SlowTool;
    #[async_trait::async_trait]
    impl forge_domain::ToolCallService for SlowTool {
        type Input = Value;

        async fn call(&self, _input: Self::Input) -> Result<String, String> {
            // Simulate a long-running task that exceeds the timeout
            tokio::time::sleep(Duration::from_secs(400)).await;
            Ok("Slow tool completed".to_string())
        }
    }

    #[tokio::test]
    async fn test_failed_tool_call_with_long_output() {
        let service = new_tool_service();
        let long_input = "all\n".repeat(TokenCounter::MAX_TOOL_OUTPUT_TOKENS + 1);
        let call = ToolCallFull {
            name: ToolName::new("long_failure_tool"),
            arguments: json!(long_input),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        assert!(result.content.contains("Output exceeds token limit"));
    }

    #[tokio::test]
    async fn test_successful_tool_call_with_long_output() {
        let service = new_tool_service();
        let long_input = "all\n".repeat(TokenCounter::MAX_TOOL_OUTPUT_TOKENS + 1);
        let call = ToolCallFull {
            name: ToolName::new("long_success_tool"),
            arguments: json!(long_input),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        assert!(result.content.contains("Output exceeds token limit"));
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

        let service = Live::from_iter(vec![slow_tool]);
        let call = ToolCallFull {
            name: ToolName::new("slow_tool"),
            arguments: json!("test input"),
            call_id: Some(ToolCallId::new("test")),
        };

        // Advance time to trigger timeout
        test::time::advance(Duration::from_secs(305)).await;

        let result = service.call(call).await;
        // Assert that the result contains a timeout error message
        let content_str = &result.content;
        assert!(
            content_str.contains("timed out"),
            "Expected timeout error message"
        );
        assert!(result.is_error, "Expected error result for timeout");
    }
}
