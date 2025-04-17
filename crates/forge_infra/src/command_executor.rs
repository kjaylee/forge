use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

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

    fn process_output(&self, output: Output) -> CommandOutput {
        CommandOutput {
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            success: output.status.success(),
        }
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
}

/// The implementation for CommandExecutorService
impl CommandExecutorService for ForgeCommandExecutorService {
    fn execute_command(
        &self,
        command: String,
        working_dir: PathBuf,
    ) -> anyhow::Result<CommandOutput> {
        let working_dir_path = Path::new(&working_dir);
        let mut cmd = self.prepare_command(&command, working_dir_path);

        // Execute the command synchronously
        let output = cmd.output()?;

        Ok(self.process_output(output))
    }

    fn execute_command_with_color(
        &self,
        command: String,
        working_dir: String,
        color_env_vars: Vec<(String, String)>,
    ) -> anyhow::Result<CommandOutput> {
        let working_dir_path = Path::new(&working_dir);
        let mut cmd = self.prepare_command(&command, working_dir_path);

        // Add all color-related environment variables
        for (key, value) in color_env_vars {
            cmd.env(key, value);
        }

        // Execute the command synchronously
        let output = cmd.output()?;

        Ok(self.process_output(output))
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
