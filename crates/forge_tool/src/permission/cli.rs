use std::fmt::Write;
use std::path::Path;
use std::time::Duration;
use forge_domain::{PermissionResult, PermissionError};
use tokio::time::timeout;
use crate::ask;

/// CLI-based permission handler that interacts with users
/// through command line interface.
#[derive(Debug, Clone)]
pub struct CliPermissionHandler {
    timeout: Duration,
}

impl Default for CliPermissionHandler {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
        }
    }
}

impl CliPermissionHandler {
    #[cfg(test)]
    pub fn new(timeout: Duration) -> Self {
        Self { timeout }
    }

    pub async fn request_permission(&self, path: &Path) -> PermissionResult<bool> {
        let mut message = String::new();
        writeln!(message, "Permission Required").unwrap();
        writeln!(message).unwrap();
        writeln!(message, "Path: {}", path.display()).unwrap();
        writeln!(message).unwrap();

        let options = vec![
            "Deny (reject)",
            "Allow",
        ];

        match timeout(
            self.timeout,
            ask::select(&message, &options)
        ).await {
            Ok(Ok(input)) => {
                let input = input.trim().to_uppercase();
                Ok(input.contains("ALLOW"))
            },
            Ok(Err(e)) => Err(PermissionError::OperationNotPermitted(e)),
            Err(e) => Err(PermissionError::OperationNotPermitted(e.to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use forge_domain::PermissionError;

    #[tokio::test]
    async fn test_timeout() {
        let handler = CliPermissionHandler::new(Duration::from_millis(1));
        let path = PathBuf::from("/test/path");

        let result = handler.request_permission(&path).await;
        assert!(matches!(result, Err(PermissionError::OperationNotPermitted(_))));
    }

}
