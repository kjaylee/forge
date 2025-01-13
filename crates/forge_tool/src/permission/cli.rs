use std::fmt::Write;
use std::time::Duration;

use forge_domain::{Permission, PermissionError, PermissionResult};
use tokio::time::timeout;
#[cfg(not(test))]
use {
    crate::select::{SelectInput, SelectTool},
    forge_domain::ToolCallService,
};

/// CLI-based permission handler that interacts with users
/// through command line interface.
#[derive(Debug, Clone)]
pub struct CliPermissionHandler {
    timeout: Duration,
}

impl Default for CliPermissionHandler {
    fn default() -> Self {
        Self { timeout: Duration::from_secs(30) }
    }
}

impl CliPermissionHandler {
    #[cfg(test)]
    pub fn new(timeout: Duration) -> Self {
        Self { timeout }
    }

    pub async fn request_permission(&self, perm: Permission, cmd: Option<&str>) -> PermissionResult<bool> {
        let mut message = String::new();
        writeln!(message, "Permission Required").unwrap();
        writeln!(message).unwrap();
        writeln!(message, "Operation: {:?}", perm).unwrap();
        if let Some(cmd) = cmd {
            writeln!(message, "Command: {}", cmd).unwrap();
        }
        writeln!(message).unwrap();

        #[cfg(not(test))]
        let options = vec!["Deny (reject)".to_string(), "Allow".to_string()];

        match timeout(self.timeout, async {
            #[cfg(test)]
            {
                tokio::time::sleep(Duration::from_secs(1)).await;
                Ok::<String, String>("Deny (reject)".to_string())
            }
            #[cfg(not(test))]
            {
                let select = SelectTool;
                let input = SelectInput { message, options };
                select.call(input).await
            }
        })
        .await
        {
            Ok(Ok(input)) => {
                let input = input.trim().to_uppercase();
                Ok(input.contains("ALLOW"))
            }
            Ok(Err(e)) => Err(PermissionError::OperationNotPermitted(e)),
            Err(e) => Err(PermissionError::OperationNotPermitted(e.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_timeout() {
        let handler = CliPermissionHandler::new(Duration::from_millis(1));
        let result = handler.request_permission(Permission::Read, None).await;
        assert!(matches!(
            result,
            Err(PermissionError::OperationNotPermitted(_))
        ));
    }

    #[tokio::test]
    async fn test_request_with_command() {
        let handler = CliPermissionHandler::new(Duration::from_secs(1));
        let result = handler
            .request_permission(Permission::Execute, Some("ls -la"))
            .await;
        // In test mode, this always returns false (deny)
        assert!(matches!(result, Ok(false)));
    }

    #[tokio::test]
    async fn test_request_without_command() {
        let handler = CliPermissionHandler::new(Duration::from_secs(1));
        let result = handler.request_permission(Permission::Read, None).await;
        // In test mode, this always returns false (deny)
        assert!(matches!(result, Ok(false)));
    }
}