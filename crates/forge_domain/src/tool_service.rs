use std::collections::HashMap;
use std::sync::Arc;

use serde_json::Value;

use crate::{Permission, Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult};

#[async_trait::async_trait]
pub trait PermissionChecker: Send + Sync {
    async fn check_permission(&self, perm: Permission, cmd: Option<&str>) -> Result<bool, String>;
}

#[async_trait::async_trait]
pub trait ToolService: Send + Sync {
    async fn call(&self, call: ToolCallFull) -> ToolResult;
    fn list(&self) -> Vec<ToolDefinition>;
    fn usage_prompt(&self) -> String;
}

pub struct Live {
    tools: HashMap<ToolName, Tool>,
    permission_checker: Arc<dyn PermissionChecker>,
}

impl Live {
    pub fn new(
        tools: impl IntoIterator<Item = Tool>,
        permission_checker: Arc<dyn PermissionChecker>,
    ) -> Self {
        let tools = tools
            .into_iter()
            .map(|tool| (tool.definition.name.clone(), tool))
            .collect();

        Self { tools, permission_checker }
    }

    async fn check_permissions(&self, tool: &Tool) -> Result<(), String> {
        let request = tool.executable.permission_check(Value::Null).await;
        for permission in &request.permissions {
            let cmd = match permission {
                Permission::Execute => Some(""), // Default command for execute permission
                _ => None,
            };

            if !self
                .permission_checker
                .check_permission(*permission, cmd)
                .await?
            {
                return Err(format!("Permission denied: {:?}", permission));
            }
        }
        Ok(())
    }
}

#[async_trait::async_trait]
impl ToolService for Live {
    async fn call(&self, call: ToolCallFull) -> ToolResult {
        let name = call.name.clone();
        let input = call.arguments.clone();
        let available_tools = self
            .tools
            .keys()
            .map(|name| name.as_str())
            .collect::<Vec<_>>()
            .join(", ");

        let output = match self.tools.get(&name) {
            Some(tool) => {
                // Check permissions before executing
                if let Err(e) = self.check_permissions(tool).await {
                    Err(e)
                } else {
                    tool.executable.call(input).await
                }
            }
            None => Err(format!(
                "No tool with name '{}' was found. Please try again with one of these tools {}",
                name.as_str(),
                available_tools
            )),
        };

        match output {
            Ok(output) => ToolResult::from(call).content(output),
            Err(error) => {
                ToolResult::from(call).content(Value::from(format!("<error>{}</error>", error)))
            }
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
