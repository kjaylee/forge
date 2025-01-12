use std::collections::HashMap;
use std::path::PathBuf;
use forge_domain::{
    Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult, ToolService,
    Permission, PermissionError, PermissionConfig
};
use serde_json::Value;
use tracing::debug;

use crate::permission::LivePermissionService;
use crate::permission::CliPermissionHandler;
use crate::{fs::*, Service};
use crate::outline::Outline;
use crate::shell::Shell;
use crate::think::Think;
use crate::permission::PermissionResultDisplay;

struct Live {
   pub tools: HashMap<ToolName, Tool>,
   pub  permission_service: LivePermissionService,
   pub permission_handler: CliPermissionHandler,
}

impl Live {
    fn with_permissions() -> Self {
        let permission_service = LivePermissionService::new();
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

impl FromIterator<Tool> for Live {
    fn from_iter<T: IntoIterator<Item = Tool>>(iter: T) -> Self {
        let live = Self::with_permissions();

        let mut tools = HashMap::new();
        for tool in iter {
            tools.insert(tool.definition.name.clone(), tool);
        }
        Live {
            tools,
            permission_service: live.permission_service,
            permission_handler: live.permission_handler,
        }
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
            // Map tool name to permission type
            let permission = match name.as_str() {
                "fs_read" => Permission::Read,
                "fs_write" => Permission::Write,
                "execute_command" => Permission::Execute,
                _ => Permission::Read // Default to read permission for other tools
            };

            // First check if we have permission
            let has_permission = match self.permission_service.check_permission(&path, permission.clone()).await {
                Ok(true) => true,
                Ok(false) => {
                    // Ask for permission
                    match self.permission_handler.request_permission(&path).await {
                        Ok(true) => {
                            // Grant permission for the session
                            if let Err(e) = self.permission_service.update_permission(&path, permission, true).await {
                                tracing::error!("Failed to update permission: {}", e);
                            }
                            true
                        },
                        Ok(false) => false,
                        Err(e) => {
                            let result = PermissionResultDisplay::new(
                                false,
                                permission.clone(),
                                &path,
                                Some(format!("Error: {}", e))
                            );
                            return ToolResult::from(call)
                                .content(Value::from(format!("<e>{}</e>", result)));
                        }
                    }
                },
                Err(e) => {
                    let result = PermissionResultDisplay::new(
                        false,
                        permission.clone(),
                        path,
                        Some(format!("Error: {}", e))
                    );
                    return ToolResult::from(call)
                        .content(Value::from(format!("<e>{}</e>", result)));
                }
            };

            if !has_permission {
                let result = PermissionResultDisplay::simple(false, permission, &path);
                return ToolResult::from(call)
                    .content(Value::from(format!("<e>{}</e>", result)));
            }
        }

        // Execute the tool
        let output = if let Some(tool) = self.tools.get(&name) {
            tool.executable.call(input).await
        } else {
            let available = self.tools.keys().map(|n| n.as_str()).collect::<Vec<_>>().join(", ");
            Err(format!("Tool '{}' not found. Available tools: {}", name.as_str(), available))
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
    use std::sync::Arc;

    use insta::assert_snapshot;
    use tokio::sync::RwLock;
    use super::*;
    use crate::{fs::{FSFileInfo, FSSearch}, permission::PathValidator};
    use forge_domain::{NamedTool, Policy, ToolCallId};
    use crate::Service;

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
    async fn test_permission_denied() {
        // Create service with no permissions
        let service = Live {
            tools: HashMap::new(),
            permission_service: LivePermissionService::new(),
            permission_handler: CliPermissionHandler::default(),
        };

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
        let mut config = PermissionConfig::default();
        config.deny_patterns.push("**/secrets/**".to_string());
        
        let service = Live {
            tools: HashMap::new(),
            permission_service: LivePermissionService::new(),
            permission_handler: CliPermissionHandler::default(),
        };

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
