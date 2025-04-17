use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use forge_services::{CommandExecutorService, CommandOutput};

/// Service for executing shell commands
#[derive(Clone, Debug)]
pub struct ForgeCommandExecutorService {
    restricted: bool,
}

impl ForgeCommandExecutorService {
    pub fn new(restricted: bool) -> Self {
        Self { restricted }
    }

    fn create_command(&self, command_str: &str) -> Command {
        let shell = if self.restricted { "rbash" } else { "bash" };
        let mut command = Command::new(shell);

        // Core color settings for general commands
        command
            .env("CLICOLOR_FORCE", "1")
            .env("FORCE_COLOR", "true")
            .env_remove("NO_COLOR");

        // Language/program specific color settings
        command
            .env("SBT_OPTS", "-Dsbt.color=always")
            .env("JAVA_OPTS", "-Dsbt.color=always");

        // enabled Git colors
        command.env("GIT_CONFIG_PARAMETERS", "'color.ui=always'");

        // Other common tools
        command.env("GREP_OPTIONS", "--color=always"); // GNU grep

        command.arg("-c").arg(command_str);

        command
    }

    fn prepare_command(&self, command_str: &str, working_dir: &Path) -> Command {
        // Create a basic command
        let mut command = self.create_command(command_str);

        // Set the working directory
        command.current_dir(working_dir);

        // Configure the command for output
        command
            .stdin(Stdio::inherit())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        command
    }

    /// Internal method to execute commands with streaming to console
    fn execute_command_internal(
        &self,
        command: String,
        working_dir: &Path,
        color_env_vars: Option<Vec<(String, String)>>,
    ) -> anyhow::Result<CommandOutput> {
        let mut cmd = self.prepare_command(&command, working_dir);
        
        // Add any additional color environment variables
        if let Some(vars) = color_env_vars {
            for (key, value) in vars {
                cmd.env(key, value);
            }
        }

        // Stream output to console while capturing it
        let mut child = cmd.spawn()?;
        
        // Use separate buffers for stdout and stderr
        let mut stdout_buffer = Vec::new();
        let mut stderr_buffer = Vec::new();
        
        // Read from stdout and write to console
        if let Some(mut stdout) = child.stdout.take() {
            let mut buffer = [0; 1024];
            while let Ok(n) = stdout.read(&mut buffer) {
                if n == 0 { break; }
                
                // Write to console
                io::stdout().write_all(&buffer[..n])?;
                io::stdout().flush()?;
                
                // Store for return value
                stdout_buffer.extend_from_slice(&buffer[..n]);
            }
        }
        
        // Read from stderr and write to console
        if let Some(mut stderr) = child.stderr.take() {
            let mut buffer = [0; 1024];
            while let Ok(n) = stderr.read(&mut buffer) {
                if n == 0 { break; }
                
                // Write to console
                io::stderr().write_all(&buffer[..n])?;
                io::stderr().flush()?;
                
                // Store for return value
                stderr_buffer.extend_from_slice(&buffer[..n]);
            }
        }
        
        // Wait for the process to complete
        let status = child.wait()?;
        
        Ok(CommandOutput {
            stdout: String::from_utf8_lossy(&stdout_buffer).into_owned(),
            stderr: String::from_utf8_lossy(&stderr_buffer).into_owned(),
            success: status.success(),
        })
    }
}

/// The implementation for CommandExecutorService
impl CommandExecutorService for ForgeCommandExecutorService {
    fn execute_command(
        &self,
        command: String,
        working_dir: PathBuf,
    ) -> anyhow::Result<CommandOutput> {
        self.execute_command_internal(command, &working_dir, None)
    }

    fn execute_command_with_color(
        &self,
        command: String,
        working_dir: String,
        color_env_vars: Vec<(String, String)>,
    ) -> anyhow::Result<CommandOutput> {
        self.execute_command_internal(command, Path::new(&working_dir), Some(color_env_vars))
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_command_executor() {
        let fixture = ForgeCommandExecutorService::new(false);
        let cmd = "echo 'hello world'";
        let dir = ".";

        let actual = fixture
            .execute_command(cmd.to_string(), PathBuf::new().join(dir))
            .unwrap();
        let expected = CommandOutput {
            stdout: "hello world\n".to_string(),
            stderr: "".to_string(),
            success: true,
        };

        assert_eq!(actual.stdout.trim(), expected.stdout.trim());
        assert_eq!(actual.stderr, expected.stderr);
        assert_eq!(actual.success, expected.success);
    }
}