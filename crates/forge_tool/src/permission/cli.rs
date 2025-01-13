use forge_domain::{Permission, PermissionResult};
#[cfg(not(test))]
use {
    crate::select::{SelectInput, SelectTool},
    forge_domain::{PermissionError, ToolCallService},
};

#[derive(Debug, Clone, Default)]
pub struct CliPermissionHandler {
    #[cfg(test)]
    test_response: Option<bool>,
}

impl CliPermissionHandler {
    #[cfg(test)]
    pub fn with_response(response: bool) -> Self {
        Self {
            test_response: Some(response),
        }
    }


    #[cfg(not(test))]
    pub async fn request_permission(&self, perm: Permission, cmd: Option<&str>) -> PermissionResult<bool> {
        let message = match cmd {
            Some(cmd) => format!("Permission Required\n\nOperation: {:?}\nCommand: {}\n", perm, cmd),
            None => format!("Permission Required\n\nOperation: {:?}\n", perm),
        };

        let options = vec!["Deny (reject)".to_string(), "Allow".to_string()];
        let select = SelectTool;
        let input = SelectInput { message, options };

        match select.call(input).await {
            Ok(input) => Ok(input.trim().to_uppercase().contains("ALLOW")),
            Err(e) => Err(PermissionError::OperationNotPermitted(e)),
        }
    }

    #[cfg(test)]
    pub async fn request_permission(&self, _perm: Permission, _cmd: Option<&str>) -> PermissionResult<bool> {
        Ok(self.test_response.unwrap_or(false))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_default_denies_permission() {
        let handler = CliPermissionHandler::default();
        let result = handler.request_permission(Permission::Read, None).await;
        assert!(matches!(result, Ok(false)), "Default should deny permission");
    }

    #[tokio::test]
    async fn test_explicit_allow_permission() {
        let handler = CliPermissionHandler::with_response(true);
        let result = handler.request_permission(Permission::Execute, Some("ls")).await;
        assert!(matches!(result, Ok(true)), "Should explicitly allow permission");
    }

    #[tokio::test]
    async fn test_explicit_deny_permission() {
        let handler = CliPermissionHandler::with_response(false);
        let result = handler.request_permission(Permission::Write, None).await;
        assert!(matches!(result, Ok(false)), "Should explicitly deny permission");
    }

    #[tokio::test]
    async fn test_all_permission_types() {
        let handler = CliPermissionHandler::with_response(true);
        
        // Test Read permission
        let read = handler.request_permission(Permission::Read, None).await;
        assert!(matches!(read, Ok(true)), "Should allow read permission");

        // Test Write permission
        let write = handler.request_permission(Permission::Write, None).await;
        assert!(matches!(write, Ok(true)), "Should allow write permission");

        // Test Execute permission with command
        let execute = handler.request_permission(Permission::Execute, Some("git status")).await;
        assert!(matches!(execute, Ok(true)), "Should allow execute permission");
    }
}