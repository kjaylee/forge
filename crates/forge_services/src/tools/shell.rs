use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::bail;
use forge_display::TitleFormat;
use forge_domain::{
    CommandOutput, Environment, EnvironmentService, ExecutableTool, NamedTool, ToolCallContext,
    ToolDescription, ToolName, TruncatedCommandOutput,
};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{CommandExecutorService, Infrastructure};

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ShellInput {
    /// The shell command to execute.
    pub command: String,
    /// The working directory where the command should be executed.
    pub cwd: PathBuf,
}

/// Formats regular command output by wrapping non-empty stdout/stderr in XML
/// tags. stderr is commonly used for warnings and progress info, so success is
/// determined by exit status, not stderr presence. Returns Ok(output) on
/// success or Err(output) on failure, with a status message if both streams are
/// empty.
fn format_output(output: CommandOutput) -> anyhow::Result<String> {
    let mut formatted_output = String::new();

    // Add stdout content if not empty
    if !output.stdout.trim().is_empty() {
        formatted_output.push_str(&format!("<stdout>{}</stdout>", output.stdout));
    }

    // Add stderr content if not empty
    if !output.stderr.trim().is_empty() {
        if !formatted_output.is_empty() {
            formatted_output.push('\n');
        }
        formatted_output.push_str(&format!("<stderr>{}</stderr>", output.stderr));
    }

    // If no formatted output yet, provide a status message
    if formatted_output.is_empty() {
        formatted_output = if output.success {
            "Command executed successfully with no output.".to_string()
        } else {
            "Command failed with no output.".to_string()
        };
    }

    if output.success {
        Ok(formatted_output)
    } else {
        Err(anyhow::anyhow!(formatted_output))
    }
}

/// Formats truncated command output with information about the truncation.
fn format_truncated_output(output: TruncatedCommandOutput) -> anyhow::Result<String> {
    let mut formatted_output = String::new();

    // Add stdout content if not empty
    if !output.stdout.trim().is_empty() {
        formatted_output.push_str(&format!("<stdout>{}</stdout>", output.stdout));
    }

    // Add stderr content if not empty
    if !output.stderr.trim().is_empty() {
        if !formatted_output.is_empty() {
            formatted_output.push('\n');
        }
        formatted_output.push_str(&format!("<stderr>{}</stderr>", output.stderr));
    }

    // Add truncation information
    if !formatted_output.is_empty() {
        formatted_output.push_str("\n\n");
    }
    formatted_output.push_str("Note: The output has been truncated.\n");
    formatted_output.push_str(&format!(
        "Original stdout size: {} characters\n",
        output.stdout_size()
    ));
    if output.stderr_size() > 0 {
        formatted_output.push_str(&format!(
            "Original stderr size: {} characters\n",
            output.stderr_size()
        ));
    }
    formatted_output.push_str("Showing first and last 20,000 characters of large outputs.\n");

    // Add information about the temp file if one exists
    if let Some(temp_path) = output.temp_file_path() {
        formatted_output.push_str(&format!(
            "\nFull output saved to: {}\n",
            temp_path.display()
        ));
    }

    // If no formatted output yet, provide a status message
    if formatted_output.is_empty() {
        formatted_output = if output.success {
            "Command executed successfully with no output.".to_string()
        } else {
            "Command failed with no output.".to_string()
        };
    }

    if output.success {
        Ok(formatted_output)
    } else {
        Err(anyhow::anyhow!(formatted_output))
    }
}

/// Executes shell commands with safety measures using restricted bash (rbash).
/// Prevents potentially harmful operations like absolute path execution and
/// directory changes. Use for file system interaction, running utilities,
/// installing packages, or executing build commands. For operations requiring
/// unrestricted access, advise users to run forge CLI with '-u' flag. Returns
/// complete output including stdout, stderr, and exit code for diagnostic
/// purposes.
#[derive(ToolDescription)]
pub struct Shell<I> {
    env: Environment,
    infra: Arc<I>,
}

impl<I: Infrastructure> Shell<I> {
    /// Create a new Shell with environment configuration
    pub fn new(infra: Arc<I>) -> Self {
        let env = infra.environment_service().get_environment();
        Self { env, infra }
    }

    /// Truncates large text output, keeping first and last portions
    fn truncate_large_text(&self, text: &str) -> (String, bool) {
        const KEEP_CHARS: usize = 20_000; // Keep 20k chars from each end
        const MAX_OUTPUT_CHARS: usize = KEEP_CHARS * 2; // 40k chars total max

        // If the text isn't large enough to truncate, just return it
        if text.len() <= MAX_OUTPUT_CHARS {
            return (text.to_string(), false);
        }

        // Text is large, so we need to truncate
        let mut result = String::with_capacity(MAX_OUTPUT_CHARS + 100); // Extra space for joining string

        // Get first KEEP_CHARS characters
        result.push_str(&text[..KEEP_CHARS]);
        // Add divider
        result.push_str("\n\n[...truncated...]\n\n");
        // Get last KEEP_CHARS characters
        let start_of_last = text.len().saturating_sub(KEEP_CHARS);
        result.push_str(&text[start_of_last..]);

        (result, true)
    }

    /// Checks if output is large enough to warrant truncation
    fn is_large_output(&self, stdout: &str, stderr: &str) -> bool {
        const SIZE_THRESHOLD: usize = 40_000; // 40k chars threshold
        (stdout.len() + stderr.len()) > SIZE_THRESHOLD
    }

    /// Creates a path for a temporary file to store the full output
    fn create_temp_file_path(&self, command: &str) -> PathBuf {
        // Get a timestamp to use in the filename
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        // Create a safe filename from the command
        let safe_command = command
            .chars()
            .map(|c| {
                if c.is_alphanumeric() || c == '-' || c == '_' {
                    c
                } else {
                    '_'
                }
            })
            .collect::<String>();

        // Truncate if the command is too long
        let safe_command = if safe_command.len() > 30 {
            safe_command[..30].to_string()
        } else {
            safe_command
        };

        // Create the filename using the timestamp and command
        let filename = format!("forge_shell_{timestamp}_{safe_command}.txt");

        // Return the full path
        self.env.base_path.join("temp_files").join(filename)
    }

    /// Writes the full output to a temporary file
    fn write_to_temp_file(&self, output: &CommandOutput, command: &str) -> anyhow::Result<PathBuf> {
        // Create a temporary file path
        let temp_dir = self.env.base_path.join("temp_files");
        if !temp_dir.exists() {
            fs::create_dir_all(&temp_dir)?;
        }

        let temp_path = self.create_temp_file_path(command);

        // Write the full output to the temporary file
        let mut file = fs::File::create(&temp_path)?;

        // Write metadata
        writeln!(file, "--- COMMAND EXECUTION OUTPUT ---")?;
        writeln!(file, "Command: {command}")?;
        writeln!(
            file,
            "Exit Code: {}",
            if output.success {
                "0 (Success)"
            } else {
                "Non-zero (Failure)"
            }
        )?;
        writeln!(file, "Timestamp: {}", chrono::Local::now().to_rfc3339())?;
        writeln!(
            file,
            "\n--- STDOUT ({} characters) ---",
            output.stdout.len()
        )?;
        write!(file, "{}", output.stdout)?;
        writeln!(
            file,
            "\n\n--- STDERR ({} characters) ---",
            output.stderr.len()
        )?;
        write!(file, "{}", output.stderr)?;

        Ok(temp_path)
    }

    /// Truncates large command output and writes the full output to a temp file
    fn truncate_command_output(
        &self,
        output: CommandOutput,
        command: &str,
    ) -> anyhow::Result<TruncatedCommandOutput> {
        // Get the stdout and stderr lengths before we move the output
        let stdout_len = output.stdout.len();
        let stderr_len = output.stderr.len();

        // Write the full output to a temporary file
        let temp_path = self.write_to_temp_file(&output, command)?;

        // Truncate stdout and stderr
        let (truncated_stdout, _) = self.truncate_large_text(&output.stdout);
        let (truncated_stderr, _) = self.truncate_large_text(&output.stderr);

        // Create new truncated output
        Ok(output.into_truncated(
            truncated_stdout,
            truncated_stderr,
            stdout_len,
            stderr_len,
            Some(temp_path),
        ))
    }
}

impl<I> NamedTool for Shell<I> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_process_shell")
    }
}

#[async_trait::async_trait]
impl<I: Infrastructure> ExecutableTool for Shell<I> {
    type Input = ShellInput;

    async fn call(&self, context: ToolCallContext, input: Self::Input) -> anyhow::Result<String> {
        // Validate empty command
        if input.command.trim().is_empty() {
            bail!("Command string is empty or contains only whitespace".to_string());
        }
        let title_format = TitleFormat::new(format!("Execute [{}]", self.env.shell.as_str()))
            .sub_title(&input.command);

        context.send_text(title_format.format()).await?;

        // Execute the command
        let output = self
            .infra
            .command_executor_service()
            .execute_command(input.command.clone(), input.cwd)
            .await?;

        // Check if the output is large enough to warrant truncation
        if self.is_large_output(&output.stdout, &output.stderr) {
            // Truncate the large output and write to temp file
            let truncated_output = self.truncate_command_output(output, &input.command)?;
            return format_truncated_output(truncated_output);
        }

        // For regular size outputs, just format the original output
        format_output(output)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::{env, fs};

    use pretty_assertions::assert_eq;

    use super::*;
    use crate::attachment::tests::MockInfrastructure;

    /// Platform-specific error message patterns for command not found errors
    #[cfg(target_os = "windows")]
    const COMMAND_NOT_FOUND_PATTERNS: [&str; 2] = [
        "is not recognized",             // cmd.exe
        "'non_existent_command' is not", // PowerShell
    ];

    #[cfg(target_family = "unix")]
    const COMMAND_NOT_FOUND_PATTERNS: [&str; 3] = [
        "command not found",               // bash/sh
        "non_existent_command: not found", // bash/sh (Alternative Unix error)
        "No such file or directory",       // Alternative Unix error
    ];

    #[tokio::test]
    async fn test_shell_echo() {
        let infra = Arc::new(MockInfrastructure::new());
        let shell = Shell::new(infra);
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "echo 'Hello, World!'".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();
        assert!(result.contains("Mock command executed successfully"));
    }

    #[tokio::test]
    async fn test_shell_stderr_with_success() {
        let infra = Arc::new(MockInfrastructure::new());
        let shell = Shell::new(infra);
        // Use a command that writes to both stdout and stderr
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: if cfg!(target_os = "windows") {
                        "echo 'to stderr' 1>&2 && echo 'to stdout'".to_string()
                    } else {
                        "echo 'to stderr' >&2; echo 'to stdout'".to_string()
                    },
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();

        assert_eq!(
            result,
            "<stdout>to stdout\n</stdout>\n<stderr>to stderr\n</stderr>"
        );
    }

    #[tokio::test]
    async fn test_shell_both_streams() {
        let infra = Arc::new(MockInfrastructure::new());
        let shell = Shell::new(infra);
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "echo 'to stdout' && echo 'to stderr' >&2".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();

        assert_eq!(
            result,
            "<stdout>to stdout\n</stdout>\n<stderr>to stderr\n</stderr>"
        );
    }

    #[tokio::test]
    async fn test_shell_with_working_directory() {
        let infra = Arc::new(MockInfrastructure::new());
        let shell = Shell::new(infra);
        let temp_dir = fs::canonicalize(env::temp_dir()).unwrap();

        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: if cfg!(target_os = "windows") {
                        "cd".to_string()
                    } else {
                        "pwd".to_string()
                    },
                    cwd: temp_dir.clone(),
                },
            )
            .await
            .unwrap();
        assert_eq!(result, format!("<stdout>{}\n</stdout>", temp_dir.display()));
    }

    #[tokio::test]
    async fn test_shell_invalid_command() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "non_existent_command".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await;

        assert!(result.is_err());
        let err = result.unwrap_err();

        // Check if any of the platform-specific patterns match
        let matches_pattern = COMMAND_NOT_FOUND_PATTERNS
            .iter()
            .any(|&pattern| err.to_string().contains(pattern));

        assert!(
            matches_pattern,
            "Error message '{err}' did not match any expected patterns for this platform: {COMMAND_NOT_FOUND_PATTERNS:?}"
        );
    }

    #[tokio::test]
    async fn test_shell_empty_command() {
        let infra = Arc::new(MockInfrastructure::new());
        let shell = Shell::new(infra);
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput { command: "".to_string(), cwd: env::current_dir().unwrap() },
            )
            .await;
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err().to_string(),
            "Command string is empty or contains only whitespace"
        );
    }

    #[tokio::test]
    async fn test_description() {
        assert!(
            Shell::new(Arc::new(MockInfrastructure::new()))
                .description()
                .len()
                > 100
        )
    }

    #[tokio::test]
    async fn test_format_output_with_truncation() {
        // Create a test truncated output
        let truncated_stdout =
            "A".repeat(20_000) + "\n\n[...truncated...]\n\n" + &"A".repeat(20_000);

        let output = TruncatedCommandOutput::new(
            truncated_stdout,
            String::new(), // No stderr
            true,          // Success
            50_000,        // Original stdout size
            0,             // Original stderr size
            None,          // No temp file
        );

        // Format the output
        let result = format_truncated_output(output).unwrap();

        // Check that the output contains the expected information
        assert!(result.contains("<stdout>"));
        assert!(result.contains("Original stdout size: 50000 characters"));
        assert!(result.contains("Showing first and last 20,000 characters"));
    }

    #[tokio::test]
    async fn test_format_output_with_temp_file() {
        // Create a test truncated output with a temp file path
        let truncated_stdout =
            "A".repeat(20_000) + "\n\n[...truncated...]\n\n" + &"A".repeat(20_000);
        let temp_path = PathBuf::from("/tmp/test_output.txt");

        let output = TruncatedCommandOutput::new(
            truncated_stdout,
            String::new(),   // No stderr
            true,            // Success
            50_000,          // Original stdout size
            0,               // Original stderr size
            Some(temp_path), // With temp file
        );

        // Format the output
        let result = format_truncated_output(output).unwrap();

        // Check that the temp file path is included in the output
        assert!(result.contains("Full output saved to: /tmp/test_output.txt"));
    }

    #[tokio::test]
    async fn test_large_output_handling() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));

        // Test truncation
        let text = "A".repeat(50_000); // 50k chars
        let (truncated, was_truncated) = shell.truncate_large_text(&text);

        assert!(was_truncated);

        // Check the truncated text pattern
        assert!(truncated.contains("[...truncated...]"));
        // Truncated size should be 40k chars + divider (\n\n[...truncated...]\n\n)
        assert_eq!(truncated.len(), 40_000 + "\n\n[...truncated...]\n\n".len());

        // Test with text below truncation threshold
        let small_text = "A".repeat(30_000);
        let (result, was_truncated) = shell.truncate_large_text(&small_text);
        assert!(!was_truncated);
        assert_eq!(result, small_text);

        // Test size threshold logic
        const TEST_THRESHOLD: usize = 40_000; // 40k chars threshold

        // Small output (below threshold)
        let small_output = "A".repeat(TEST_THRESHOLD - 1);
        assert!(!shell.is_large_output(&small_output, ""));

        // Large output (just above threshold)
        let large_output = "A".repeat(TEST_THRESHOLD + 1);
        assert!(shell.is_large_output(&large_output, ""));

        // Combined output crossing threshold
        let part1 = "A".repeat(TEST_THRESHOLD / 2);
        let part2 = "B".repeat(TEST_THRESHOLD / 2 + 1);
        assert!(shell.is_large_output(&part1, &part2));
    }

    #[tokio::test]
    async fn test_temp_file_path_generation() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));

        // Test with a normal command
        let path1 = shell.create_temp_file_path("ls -la");
        assert!(path1.to_string_lossy().contains("forge_shell_"));

        let filename = path1.file_name().unwrap().to_string_lossy();
        assert!(filename.contains("forge_shell_"));

        // Note: spaces are converted to underscores, so "ls -la" becomes "ls_-la" in
        // the filename We're just verifying it contains the command part in
        // some form
        assert!(filename.contains("ls_"));

        // Test with a long command that should be truncated
        let long_command =
            "this_is_a_very_long_command_that_should_be_truncated_to_30_characters_at_most";
        let path2 = shell.create_temp_file_path(long_command);
        let filename = path2.file_name().unwrap().to_string_lossy();
        // The command part should be truncated to 30 chars
        assert!(filename.len() < long_command.len() + 20); // Add some buffer for the timestamp

        // The path should use the base_path and temp_files directory
        assert!(path1.starts_with(&shell.env.base_path));
        assert!(path1.to_string_lossy().contains("temp_files"));
    }

    #[tokio::test]
    async fn test_shell_pwd() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        let current_dir = env::current_dir().unwrap();
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: if cfg!(target_os = "windows") {
                        "cd".to_string()
                    } else {
                        "pwd".to_string()
                    },
                    cwd: current_dir.clone(),
                },
            )
            .await
            .unwrap();

        assert_eq!(
            result,
            format!("<stdout>{}\n</stdout>", current_dir.display())
        );
    }

    #[tokio::test]
    async fn test_shell_multiple_commands() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "echo 'first' && echo 'second'".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();
        assert_eq!(result, format!("<stdout>first\nsecond\n</stdout>"));
    }

    #[tokio::test]
    async fn test_shell_empty_output() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "true".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();

        assert!(result.contains("executed successfully"));
        assert!(!result.contains("failed"));
    }

    #[tokio::test]
    async fn test_shell_whitespace_only_output() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "echo ''".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();

        assert!(result.contains("executed successfully"));
        assert!(!result.contains("failed"));
    }

    #[tokio::test]
    async fn test_shell_with_environment_variables() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput {
                    command: "echo $PATH".to_string(),
                    cwd: env::current_dir().unwrap(),
                },
            )
            .await
            .unwrap();

        assert!(!result.is_empty());
        assert!(!result.contains("Error:"));
    }

    #[tokio::test]
    async fn test_shell_full_path_command() {
        let shell = Shell::new(Arc::new(MockInfrastructure::new()));
        // Using a full path command which would be restricted in rbash
        let cmd = if cfg!(target_os = "windows") {
            r"C:\Windows\System32\whoami.exe"
        } else {
            "/bin/ls"
        };

        let result = shell
            .call(
                ToolCallContext::default(),
                ShellInput { command: cmd.to_string(), cwd: env::current_dir().unwrap() },
            )
            .await;

        // In rbash, this would fail with a permission error
        // For our normal shell test, it should succeed
        assert!(
            result.is_ok(),
            "Full path commands should work in normal shell"
        );
    }
}
