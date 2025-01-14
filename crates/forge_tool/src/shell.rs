use std::path::PathBuf;

use anyhow::Result;
use forge_domain::{NamedTool, ToolCallService, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use tokio::process::Command;

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ShellInput {
    /// The shell command to execute.
    pub command: String,
    /// The working directory where the command should be executed.
    pub cwd: PathBuf,
}

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ShellOutput {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdout: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stderr: Option<String>,
    pub success: bool,
}


/// A tool to execute shell commands on the host system.
///
/// ## Use Cases
/// - **System Operations**: Manage resources, monitor processes, or run administrative tasks.
/// - **File Management**: Create, modify, or organize files and directories.
/// - **Integration**: Invoke external tools or scripts.
/// - **Automation**: Automate repetitive shell-level tasks.
#[derive(ToolDescription)]
pub struct Shell;

impl Shell {
    async fn execute_command(&self, command: &str, cwd: PathBuf) -> Result<ShellOutput, String> {
        let mut cmd = if cfg!(target_os = "windows") {
            let mut c = Command::new("cmd");
            c.args(["/C", command]);
            c
        } else {
            let mut c = Command::new("sh");
            c.args(["-c", command]);
            c
        };

        cmd.current_dir(cwd);

        let output = cmd.output().await.map_err(|e| e.to_string())?;

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        Ok(ShellOutput {
            stdout: if stdout.is_empty() {
                None
            } else {
                Some(stdout)
            },
            stderr: if stderr.is_empty() {
                None
            } else {
                Some(stderr)
            },
            success: output.status.success(),
        })
    }
}

impl NamedTool for Shell {
    fn tool_name(&self) -> ToolName {
        ToolName::new("execute_command")
    }
}

#[async_trait::async_trait]
impl ToolCallService for Shell {
    type Input = ShellInput;
    type Output = ShellOutput;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        if input.command.trim().is_empty() {
            return Err("Empty command".to_string());
        }
        self.execute_command(&input.command, input.cwd).await
    }
}

#[cfg(test)]
mod tests {
    use std::{env, fs};

    use pretty_assertions::assert_eq;

    use super::*;

    #[tokio::test]
    async fn test_shell_echo() {
        let shell = Shell;
        let result = shell
            .call(ShellInput {
                command: "echo 'Hello, World!'".to_string(),
                cwd: env::current_dir().unwrap(),
            })
            .await
            .unwrap();

        assert!(result.success);
        assert!(result.stdout.as_ref().unwrap().contains("Hello, World!"));
        assert!(result.stderr.is_none());
    }

    #[tokio::test]
    async fn test_shell_with_working_directory() {
        let shell = Shell;
        let temp_dir = fs::canonicalize(env::temp_dir()).unwrap();

        let result = shell
            .call(ShellInput {
                command: if cfg!(target_os = "windows") {
                    "cd".to_string()
                } else {
                    "pwd".to_string()
                },
                cwd: temp_dir.clone(),
            })
            .await
            .unwrap();

        assert!(result.success);
        let output_path = PathBuf::from(result.stdout.as_ref().unwrap().trim());
        let actual_path = match fs::canonicalize(output_path.clone()) {
            Ok(path) => path,
            Err(_) => output_path,
        };
        let expected_path = temp_dir.as_path();

        assert_eq!(
            actual_path, expected_path,
            "\nExpected path: {:?}\nActual path: {:?}",
            expected_path, actual_path
        );
        assert!(result.stderr.is_none());
    }

    #[tokio::test]
    async fn test_shell_invalid_command() {
        let shell = Shell;
        let result = shell
            .call(ShellInput {
                command: "nonexistentcommand".to_string(),
                cwd: env::current_dir().unwrap(),
            })
            .await
            .unwrap();

        assert!(!result.success);
        assert!(result.stderr.is_some());
    }

    #[tokio::test]
    async fn test_shell_empty_command() {
        let shell = Shell;
        let result = shell
            .call(ShellInput { command: "".to_string(), cwd: env::current_dir().unwrap() })
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Empty command"));
    }

    #[tokio::test]
    async fn test_shell_pwd() {
        let shell = Shell;
        let current_dir = fs::canonicalize(env::current_dir().unwrap()).unwrap();
        let result = shell
            .call(ShellInput {
                command: if cfg!(target_os = "windows") {
                    "cd".to_string()
                } else {
                    "pwd".to_string()
                },
                cwd: current_dir.clone(),
            })
            .await
            .unwrap();

        assert!(result.success);
        let output_path = PathBuf::from(result.stdout.as_ref().unwrap().trim());
        let actual_path = fs::canonicalize(output_path.clone()).unwrap_or_else(|_| output_path);
        assert_eq!(actual_path, current_dir);
        assert!(result.stderr.is_none());
    }

    #[tokio::test]
    async fn test_shell_multiple_commands() {
        let shell = Shell;
        let result = shell
            .call(ShellInput {
                command: "echo 'first' && echo 'second'".to_string(),
                cwd: env::current_dir().unwrap(),
            })
            .await
            .unwrap();

        assert!(result.success);
        assert!(result.stdout.as_ref().unwrap().contains("first"));
        assert!(result.stdout.as_ref().unwrap().contains("second"));
        assert!(result.stderr.is_none());
    }

    #[tokio::test]
    async fn test_shell_with_environment_variables() {
        let shell = Shell;
        let result = shell
            .call(ShellInput {
                command: "echo $PATH".to_string(),
                cwd: env::current_dir().unwrap(),
            })
            .await
            .unwrap();

        assert!(result.success);
        assert!(result.stdout.is_some());
        assert!(result.stderr.is_none());
    }

    #[test]
    fn test_description() {
        assert!(Shell.description().len() > 100)
    }
}
