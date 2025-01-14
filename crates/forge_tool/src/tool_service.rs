use std::collections::HashMap;
use std::sync::Arc;

use forge_domain::{
    Permission, Tool, ToolCallFull, ToolDefinition, ToolName, ToolResult,
    ToolService,
};
use serde_json::Value;
use tracing::debug;

use crate::approve::Approve;
use crate::fs::*;
use crate::outline::Outline;
use crate::permission::{CliPermissionHandler, PermissionService};
use crate::select::SelectTool;
use crate::shell::Shell;
use crate::think::Think;
use crate::Service;

struct Live {
    pub tools: HashMap<ToolName, Tool>,
    pub permission_service: Arc<dyn PermissionService>,
    pub permission_handler: CliPermissionHandler,
}

impl Live {
    fn with_permissions() -> Self {
        let permission_service = Service::permission_service();
        let permission_handler = CliPermissionHandler::default();
        Self {
            tools: HashMap::new(),
            permission_service,
            permission_handler,
        }
    }

    async fn check_permissions(&self, tool: &Tool, args: &Value) -> Result<(), String> {
        let request = tool.executable.permission_check(args.clone());
        for permission in &request.permissions {
            let cmd = match *permission {
                Permission::Execute => request.cmd.clone(),
                _ => None,
            };

            let has_permission = self
                .permission_service
                .check_permission(*permission, cmd.as_deref())
                .await
                .map_err(|e| format!("Permission check error: {}", e))?;
            if !has_permission {
                debug!("Permission check failed for {:?}", permission);
                if !self
                    .permission_handler
                    .request_permission(*permission, cmd.as_deref())
                    .await
                    .map_err(|e| format!("Permission request error: {}", e))?
                {
                    return Err(format!("Permission denied for {:?}", permission));
                }
            }
        }
        Ok(())
    }
}

impl Live {
    pub fn from_tools<T: IntoIterator<Item = Tool>>(iter: T) -> Self {
        let mut live = Self::with_permissions();
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

        // Check permissions with command context
        if let Err(e) = self.check_permissions(tool, &input).await {
            return ToolResult::from(call).content(Value::from(format!("<e>{}</e>", e)));
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
    pub fn tool_service() -> impl ToolService {
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
        let service = Live::from_tools([Tool::new(FSRead)]);

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
        let service = Live::from_tools([Tool::new(FSRead)]);

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
