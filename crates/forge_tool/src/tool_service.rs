use std::collections::HashMap;
use std::path::PathBuf;
use forge_domain::{
    Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult, ToolService,
    PermissionRequest, PermissionState, PermissionError, PermissionInteraction,
    Permission, PermissionStorage
};
use serde_json::Value;
use tracing::debug;

use crate::permission::PermissionManager;
use crate::permission::{SessionStorage, ConfigStorage, CliPermissionHandler};
use crate::{fs::*, Service};
use crate::outline::Outline;
use crate::shell::Shell;
use crate::think::Think;
use crate::permission::PermissionResultDisplay;

struct Live {
    tools: HashMap<ToolName, Tool>,
    permission_manager: PermissionManager,
    permission_handler: CliPermissionHandler,
}

impl Live {
    fn with_permissions() -> Self {
        let session_storage = SessionStorage::new();
        let config_dir = dirs::config_dir()
            .unwrap_or_else(|| {
                let mut path = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
                path.push(".config");
                path
            })
            .join("forge");
        // Create config directory if it doesn't exist
        std::fs::create_dir_all(&config_dir).unwrap_or_else(|_| ());
        let config_path = config_dir.join("permissions.yml");
        tracing::debug!("Using permissions config file: {:?}", config_path);
        let config_storage = ConfigStorage::new(config_path);
        let permission_manager = PermissionManager::new(session_storage, config_storage);
        let permission_handler = CliPermissionHandler::default();
        Self {
            tools: HashMap::new(),
            permission_manager,
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
            permission_manager: live.permission_manager,
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
            let request = PermissionRequest::new(
                path,
                name.as_str().to_string(),
                "execute".to_string()
            );

            // First check if we have permission
            let has_permission = match self.permission_manager.check_permission(&request).await {
                Ok(state) => matches!(state, 
                    PermissionState::Allow | 
                    PermissionState::AllowSession | 
                    PermissionState::AllowForever
                ),
                Err(PermissionError::SystemDenied(_)) => {
                    // Ask for permission
                    match self.permission_handler.request_permission(&request).await {
                        Ok(state) => {
                            match state {
                                PermissionState::Allow | 
                                PermissionState::AllowSession | 
                                PermissionState::AllowForever => {
                                    tracing::debug!("User granted permission with state: {:?}", state);
                                    
                                    // Create and save the permission with the granted state
                                    let permission = Permission::new(
                                        state.clone(),
                                        request.path().to_path_buf(),
                                        request.tool_name().to_string(),
                                    );
                                    tracing::debug!("Created permission: {:?}", permission);

                                    // Save the granted permission
                                    if let Err(e) = self.permission_manager.save_permission(permission).await {
                                        tracing::error!("Failed to save permission: {}", e);
                                        return ToolResult::from(call)
                                            .content(Value::from(format!("<e>{}</e>", e)));
                                    }
                                    tracing::debug!("Successfully saved permission");
                                    true
                                },
                                PermissionState::Reject => {
                                    let result = PermissionResultDisplay::simple(PermissionState::Reject, request);
                                    return ToolResult::from(call)
                                        .content(Value::from(format!("<e>{}</e>", result)));
                                }
                            }
                        },
                        Err(e) => {
                            return ToolResult::from(call)
                                .content(Value::from(format!("<e>{}</e>", e)));
                        }
                    }
                },
                Err(e) => {
                    return ToolResult::from(call)
                        .content(Value::from(format!("<e>{}</e>", e)));
                }
            };

            // If we don't have permission, return early
            if !has_permission {
                let result = PermissionResultDisplay::simple(PermissionState::Reject, request);
                return ToolResult::from(call)
                    .content(Value::from(format!("<e>{}</e>", result)));
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
    use forge_domain::{NamedTool, ToolCallId};
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
    async fn test_permission_check() {
        let temp_dir = tempfile::tempdir().unwrap();
        let test_path = temp_dir.path().join("test.txt");
        
        // Create an empty tools list first
        let service = Live::with_permissions();

        // Write test file and ensure it exists
        let test_content = "test content";
        tokio::fs::write(&test_path, test_content).await.unwrap();
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await; // Wait for write to complete
        assert!(test_path.exists());

        // Get canonicalized path for consistent comparison
        let canonical_path = std::fs::canonicalize(&test_path).unwrap();
        let tool_name = FSRead.tool_name().as_str().to_string();

        // Create and register FSRead tool for test
        let mut tools = HashMap::new();
        tools.insert(FSRead.tool_name(), Tool::new(FSRead));
        let service = Live {
            tools,
            permission_manager: service.permission_manager,
            permission_handler: service.permission_handler,
        };

        // Create and save permission
        let permission = Permission::new(
            PermissionState::AllowForever,
            canonical_path.clone(),
            tool_name.clone(),
        );
        service.permission_manager.save_permission(permission).await.unwrap();

        // Create tool call with canonicalized path
        let call = ToolCallFull {
            name: FSRead.tool_name(),
            arguments: serde_json::json!({
                "path": canonical_path.to_string_lossy()
            }),
            call_id: Some(ToolCallId::new("test")),
        };

        // Make the call
        let result = service.call(call).await;
        let content_str = result.content.as_str().unwrap_or("");

        // Verify result
        assert!(!content_str.contains("Permission denied"));
        assert!(!content_str.contains("System denied"));
        assert_eq!(content_str, test_content);
    }

    #[tokio::test]
    async fn test_permission_denied() {
        let temp_dir = tempfile::tempdir().unwrap();
        let config_path = temp_dir.path().join("permissions.yml");
        let session_storage = SessionStorage::new();
        let config_storage = ConfigStorage::new(config_path);
        let permission_manager = PermissionManager::new(session_storage, config_storage);
        let permission_handler = CliPermissionHandler::default();
        let service = Live {
            tools: HashMap::new(),
            permission_manager,
            permission_handler,
        };

        let call = ToolCallFull {
            name: FSRead.tool_name(),
            arguments: serde_json::json!({
                "path": "/unauthorized/path"
            }),
            call_id: Some(ToolCallId::new("test")),
        };

        let result = service.call(call).await;
        println!("Response: {}", result.content);
        assert!(result.content.to_string().contains("Permission denied"));
    }
}
