use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use forge_domain::{Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult, ToolService};
use serde_json::Value;
use tracing::debug;

use crate::approve::Approve;
use crate::fs::*;
use crate::outline::Outline;
use crate::permission::{CliPermissionHandler, LivePermissionService, PermissionResultDisplay};
use crate::select::SelectTool;
use crate::shell::Shell;
use crate::think::Think;
use crate::Service;

struct Live {
    pub tools: HashMap<ToolName, Tool>,
    pub permission_service: Arc<LivePermissionService>,
    pub permission_handler: CliPermissionHandler,
}

impl Live {
    async fn with_permissions() -> Self {
        let permission_service = Arc::new(LivePermissionService::new().await);
        let permission_handler = CliPermissionHandler::default();
        Self {
            tools: HashMap::new(),
            permission_service,
            permission_handler,
        }
    }

    fn extract_path_from_args(args: &Value) -> Option<PathBuf> {
        // Try "path" field first (used by fs tools)
        if let Some(path) = args.get("path").and_then(|v| v.as_str()) {
            return Some(PathBuf::from(path));
        }
        // Try "cwd" field (used by shell tool)
        if let Some(path) = args.get("cwd").and_then(|v| v.as_str()) {
            return Some(PathBuf::from(path));
        }
        None
    }
}

impl Live {
    pub async fn from_tools<T: IntoIterator<Item = Tool>>(iter: T) -> Self {
        let mut live = Self::with_permissions().await;
        let tools: HashMap<ToolName, Tool> = iter
            .into_iter()
            .map(|tool| (tool.definition.name.clone(), tool))
            .collect::<HashMap<_, _>>();
        live.tools = tools;
        live
    }
}

#[async_trait::async_trait]
impl ToolService for Live {
    async fn call(&self, call: ToolCallFull) -> ToolResult {
        let name = call.name.clone();
        let input = call.arguments.clone();
        debug!("Calling tool: {}", name.as_str());

        // Get tool definition
        let tool = if let Some(tool) = self.tools.get(&name) {
            tool
        } else {
            let available = self
                .tools
                .keys()
                .map(|n| n.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            return ToolResult::from(call).content(Value::from(format!(
                "<e>Tool '{}' not found. Available tools: {}</e>",
                name.as_str(),
                available
            )));
        };

        // Check permissions if path is provided
        if let Some(path) = Self::extract_path_from_args(&input) {
            // Check each required permission
            for &permission in &tool.definition.required_permissions {
                let has_permission = self
                    .permission_service
                    .check_permission(&path, permission)
                    .await;

                // Handle permission check errors
                if let Err(e) = has_permission {
                    let result = PermissionResultDisplay::new(
                        false,
                        permission,
                        path.clone(),
                        Some(format!("Error: {}", e)),
                    );
                    return ToolResult::from(call.clone())
                        .content(Value::from(format!("<e>{}</e>", result)));
                }

                // Unwrap the Ok value since we've handled the error case
                let has_permission = has_permission.unwrap();

                if !has_permission {
                    // Ask for permission
                    match self.permission_handler.request_permission(&path).await {
                        Ok(true) => {
                            // Grant permission for the session
                            if let Err(e) = self
                                .permission_service
                                .update_permission(&path, permission, true)
                                .await
                            {
                                tracing::error!("Failed to update permission: {}", e);
                                let result = PermissionResultDisplay::new(
                                    false,
                                    permission,
                                    &path,
                                    Some(format!("Error: {}", e)),
                                );
                                return ToolResult::from(call)
                                    .content(Value::from(format!("<e>{}</e>", result)));
                            }
                        }
                        Ok(false) => {
                            let result = PermissionResultDisplay::simple(false, permission, &path);
                            return ToolResult::from(call)
                                .content(Value::from(format!("<e>{}</e>", result)));
                        }
                        Err(e) => {
                            let result = PermissionResultDisplay::new(
                                false,
                                permission,
                                &path,
                                Some(format!("Error: {}", e)),
                            );
                            return ToolResult::from(call)
                                .content(Value::from(format!("<e>{}</e>", result)));
                        }
                    }
                }
            }
        }

        // Execute the tool
        match tool.executable.call(input).await {
            Ok(output) => ToolResult::from(call).content(output),
            Err(error) => ToolResult::from(call).content(Value::from(format!("<e>{}</e>", error))),
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
    pub async fn tool_service() -> impl ToolService {
        Live::from_tools([
            Tool::new(Approve),
            Tool::new(FSRead),
            Tool::new(FSWrite),
            Tool::new(FSList),
            Tool::new(FSSearch),
            Tool::new(FSFileInfo),
            Tool::new(FSReplace),
            Tool::new(Outline),
            Tool::new(SelectTool),
            Tool::new(Shell::default()),
            Tool::new(Think::default()),
        ])
        .await
    }
}

#[cfg(test)]
mod test {
    use forge_domain::{NamedTool, ToolCallId};
    use insta::assert_snapshot;

    use super::*;
    use crate::fs::{FSFileInfo, FSSearch};

    #[test]
    fn test_id() {
        assert!(Tool::new(FSRead)
            .definition
            .name
            .into_string()
            .ends_with("read_file"));
        assert!(Tool::new(FSSearch)
            .definition
            .name
            .into_string()
            .ends_with("search_in_files"));
        assert!(Tool::new(FSList)
            .definition
            .name
            .into_string()
            .ends_with("list_directory_content"));
        assert!(Tool::new(FSFileInfo)
            .definition
            .name
            .into_string()
            .ends_with("file_information"));
    }

    #[tokio::test]
    async fn test_usage_prompt() {
        let service = Live::from_tools([Tool::new(FSRead), Tool::new(FSWrite)]).await;
        let prompt = service.usage_prompt();
        assert_snapshot!(prompt);
    }

    #[tokio::test]
    async fn test_tool_definition() {
        let service = Live::from_tools([Tool::new(FSRead), Tool::new(FSWrite)]).await;
        let tools = service.list();
        assert_snapshot!(serde_json::to_string_pretty(&tools).unwrap());
    }

    #[tokio::test]
    async fn test_permission_denied() {
        // Create service with no permissions
        let service = Live::from_tools([Tool::new(FSRead)]).await;

        let call = ToolCallFull {
            name: FSRead.tool_name(),
            arguments: serde_json::json!({
                "path": "/unauthorized/path"
            }),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        assert!(result.content.to_string().contains("Permission denied"));
    }

    #[tokio::test]
    async fn test_deny_patterns() {
        let temp_dir = tempfile::tempdir().unwrap();
        let secret_path = temp_dir.path().join("secrets").join("test.txt");

        // Create service with deny pattern
        let service = Live::from_tools([Tool::new(FSRead)]).await;

        let call = ToolCallFull {
            name: FSRead.tool_name(),
            arguments: serde_json::json!({
                "path": secret_path.to_string_lossy()
            }),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        assert!(result.content.to_string().contains("Permission denied"));
    }
}
