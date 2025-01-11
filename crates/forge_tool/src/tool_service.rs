use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use forge_domain::{
    Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult, ToolService,
    PermissionService, TestPermissionService,
};
use serde_json::Value;
use tracing::debug;

use crate::fs::*;
use crate::outline::Outline;
use crate::shell::Shell;
use crate::think::Think;
use crate::Service;

#[cfg(test)]
fn default_test_service() -> impl PermissionService {
    TestPermissionService::new()
}

struct Live {
    tools: HashMap<ToolName, Tool>,
    permission_service: Arc<dyn PermissionService>,
}

impl Live {
    fn with_permissions(permission_service: impl PermissionService + 'static) -> Self {
        Self {
            tools: HashMap::new(),
            permission_service: Arc::new(permission_service),
        }
    }

    fn extract_path_from_args(args: &Value) -> Option<PathBuf> {
        args.get("path")
            .and_then(|v| v.as_str())
            .map(PathBuf::from)
    }
}

impl FromIterator<Tool> for Live {
    fn from_iter<T: IntoIterator<Item = Tool>>(iter: T) -> Self {
        #[cfg(test)]
        let mut live = Self::with_permissions(default_test_service());

        #[cfg(not(test))]
        let mut live = {
            use forge_domain::Service;
            Self::with_permissions(Service::permission_service().unwrap())
        };

        live.tools = iter
            .into_iter()
            .map(|tool| (tool.definition.name.clone(), tool))
            .collect();
        live
    }
}

#[async_trait::async_trait]
impl ToolService for Live {
    async fn call(&self, call: ToolCallFull) -> ToolResult {
        let name = call.name.clone();
        let input = call.arguments.clone();
        debug!("Calling tool: {}", name.as_str());

        // Check permissions if needed
        if let Some(path) = Self::extract_path_from_args(&input) {
            if let Err(e) = self.permission_service
                .validate_path_access(path, name.as_str().to_string())
                .await 
            {
                return ToolResult::from(call)
                    .content(Value::from(format!("<e>{}</e>", e)));
            }
        }

        let available_tools = self
            .tools
            .keys()
            .map(|name| name.as_str())
            .collect::<Vec<_>>()
            .join(", ");

        let output = match self.tools.get(&name) {
            Some(tool) => tool.executable.call(input).await,
            None => Err(format!(
                "No tool with name '{}' was found. Please try again with one of these tools {}",
                name.as_str(),
                available_tools
            )),
        };

        match output {
            Ok(output) => ToolResult::from(call).content(output),
            Err(error) => {
                ToolResult::from(call).content(Value::from(format!("<e>{}</e>", error)))
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

impl Service {
    pub fn tool_service() -> impl ToolService {
        Live::from_iter([
            Tool::new(FSRead),
            Tool::new(FSWrite),
            Tool::new(FSList),
            Tool::new(FSSearch),
            Tool::new(FSFileInfo),
            Tool::new(FSReplace),
            Tool::new(Outline),
            Tool::new(Shell::default()),
            Tool::new(Think::default()),
        ])
    }
}

#[cfg(test)]
mod test {
    use insta::assert_snapshot;
    use super::*;
    use crate::fs::{FSFileInfo, FSSearch};
    use forge_domain::{Permission, PermissionState, NamedTool, ToolCallId};

    #[test]
    fn test_id() {
        assert!(Tool::new(FSRead)
            .definition
            .name
            .into_string()
            .ends_with("fs_read"));
        assert!(Tool::new(FSSearch)
            .definition
            .name
            .into_string()
            .ends_with("fs_search"));
        assert!(Tool::new(FSList)
            .definition
            .name
            .into_string()
            .ends_with("fs_list"));
        assert!(Tool::new(FSFileInfo)
            .definition
            .name
            .into_string()
            .ends_with("file_info"));
    }

    #[test]
    fn test_usage_prompt() {
        let docs = Service::tool_service().usage_prompt();
        assert_snapshot!(docs);
    }

    #[test]
    fn test_tool_definition() {
        let tools = Service::tool_service().list();
        assert_snapshot!(serde_json::to_string_pretty(&tools).unwrap());
    }

    #[tokio::test]
    async fn test_permission_check() {
        let test_path = PathBuf::from("/test/path");
        let tool_name = FSRead.tool_name().as_str().to_string();

        let permission = Permission::new(
            PermissionState::AllowOnce,
            test_path.clone(),
            tool_name.clone(),
        );

        let service = Live::with_permissions(
            TestPermissionService::new()
                .with_permission(permission)
        );

        // Create a tool call with the test path
        let call = ToolCallFull {
            name: FSRead.tool_name(),
            arguments: serde_json::json!({
                "path": "/test/path"
            }),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        // Error will be from FSRead operation, as permission check passed
        assert!(!result.content.to_string().contains("Access denied"));
    }

    #[tokio::test]
    async fn test_permission_denied() {
        let service = Live::with_permissions(TestPermissionService::new());

        let call = ToolCallFull {
            name: FSRead.tool_name(),
            arguments: serde_json::json!({
                "path": "/unauthorized/path"
            }),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        println!("Response: {}", result.content);
        assert!(result.content.to_string().contains("Access denied"));
    }
}