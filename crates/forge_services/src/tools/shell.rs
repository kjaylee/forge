use std::path::PathBuf;
use std::sync::Arc;

use anyhow::bail;
use forge_display::TitleFormat;
use forge_domain::{
    CommandOutput, Environment, EnvironmentService, ExecutableTool, NamedTool, ToolCallContext,
    ToolDescription, ToolName,
};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use strip_ansi_escapes::strip;

use crate::{
    metadata::Metadata, CommandExecutorService, Infrastructure, TempWriter, TruncationResult,
    Truncator,
};

/// Number of characters to keep at the start of truncated output
const PREFIX_CHARS: usize = 20_000;

/// Number of characters to keep at the end of truncated output
const SUFFIX_CHARS: usize = 20_000;

#[derive(Debug, Serialize, Deserialize, Clone, JsonSchema)]
pub struct ShellInput {
    /// The shell command to execute.
    pub command: String,
    /// The working directory where the command should be executed.
    pub cwd: PathBuf,
    /// Whether to preserve ANSI escape codes in the output.
    /// If true, ANSI escape codes will be preserved in the output.
    /// If false (default), ANSI escape codes will be stripped from the output.
    #[serde(default)]
    pub keep_ansi: bool,
}

// Strips out the ansi codes from content.
fn strip_ansi(content: String) -> String {
    String::from_utf8_lossy(&strip(content.as_bytes())).into_owned()
}

/// Formats command output by wrapping non-empty stdout/stderr in XML tags.
/// stderr is commonly used for warnings and progress info, so success is
/// determined by exit status, not stderr presence. Returns Ok(output) on
/// success or Err(output) on failure, with a status message if both streams are
/// empty.
async fn format_output<F: Infrastructure>(
    infra: &Arc<F>,
    mut output: CommandOutput,
    keep_ansi: bool,
) -> anyhow::Result<String> {
    let mut formatted_output = String::new();

    if !keep_ansi {
        output.stderr = strip_ansi(output.stderr);
        output.stdout = strip_ansi(output.stdout);
    }

    // Create metadata
    let mut metadata = Metadata::default()
        .add("command", &output.command)
        .add("exit_code", if output.success { 0 } else { 1 });

    let mut is_truncated = false;

    // Format stdout if not empty
    if !output.stdout.trim().is_empty() {
        let result = Truncator::from_prefix_suffix(PREFIX_CHARS, SUFFIX_CHARS, &output.stdout);

        if result.is_truncated() {
            metadata = metadata.add("total_stdout_chars", output.stdout.len());
            is_truncated = true;
        }
        format_tag(result, "stdout", &output.stdout, &mut formatted_output);
    }

    // Format stderr if not empty
    if !output.stderr.trim().is_empty() {
        if !formatted_output.is_empty() {
            formatted_output.push('\n');
        }
        let result = Truncator::from_prefix_suffix(PREFIX_CHARS, SUFFIX_CHARS, &output.stdout);

        if result.is_truncated() {
            metadata = metadata.add("total_stderr_chars", output.stderr.len());
            is_truncated = true;
        }
        format_tag(result, "stderr", &output.stderr, &mut formatted_output);
    }

    // Handle empty outputs
    if formatted_output.is_empty() {
        if output.success {
            formatted_output.push_str("Command executed successfully with no output.");
        } else {
            formatted_output.push_str("Command failed with no output.");
        }
    }

    // Add temp file path if output is truncated
    if is_truncated {
        let path = TempWriter::new(infra.clone())
            .write(
                "forge_shell_",
                &format!(
                    "<stdout>{}</stdout>\n<stderr>{}</stderr>",
                    output.stdout, output.stderr
                ),
            )
            .await?;
        metadata = metadata
            .add("temp_file", path.display())
            .add("truncated", "true");
        formatted_output.push_str(&format!(
            "<truncate>content is truncated, remaining content can be read from path:{}</truncate>",
            path.display()
        ));
    }

    if output.success {
        Ok(format!("{metadata}{formatted_output}"))
    } else {
        bail!(format!("{metadata}{formatted_output}"))
    }
}

/// Helper function to format potentially truncated output for stdout or stderr
fn format_tag(result: TruncationResult, tag: &str, content: &str, formatted_output: &mut String) {
    match (result.prefix, result.suffix) {
        (Some(prefix), Some(suffix)) => {
            // Calculate actual character counts and ranges
            let content_len = content.len();
            let prefix_len = prefix.len();
            let suffix_len = suffix.len();
            let truncated_chars = content_len - prefix_len - suffix_len;
            let suffix_start = content_len - suffix_len;

            formatted_output.push_str(&format!(
                "<{} chars=\"0-{}\">\n{}\n</{}>\n",
                tag, prefix_len, prefix, tag
            ));
            formatted_output.push_str(&format!(
                "<truncated>...{} truncated ({} characters not shown)...</truncated>\n",
                tag, truncated_chars
            ));
            formatted_output.push_str(&format!(
                "<{} chars=\"{}-{}\">\n{}\n</{}>\n",
                tag, suffix_start, content_len, suffix, tag
            ));
        }
        _ => formatted_output.push_str(&format!("<{}>\n{}\n</{}>", tag, content, tag)),
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
        let title_format = TitleFormat::debug(format!("Execute [{}]", self.env.shell.as_str()))
            .sub_title(&input.command);

        context.send_text(title_format).await?;

        let output = self
            .infra
            .command_executor_service()
            .execute_command(input.command, input.cwd)
            .await?;

        format_output(&self.infra, output, input.keep_ansi).await
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                ShellInput {
                    command: "".to_string(),
                    cwd: env::current_dir().unwrap(),
                    keep_ansi: true,
                },
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                    keep_ansi: true,
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
                ShellInput {
                    command: cmd.to_string(),
                    cwd: env::current_dir().unwrap(),
                    keep_ansi: true,
                },
            )
            .await;

        // In rbash, this would fail with a permission error
        // For our normal shell test, it should succeed
        assert!(
            result.is_ok(),
            "Full path commands should work in normal shell"
        );
    }

    #[tokio::test]
    async fn test_format_output_ansi_handling() {
        let infra = Arc::new(MockInfrastructure::new());
        // Test with keep_ansi = true (should preserve ANSI codes)
        let ansi_output = CommandOutput {
            stdout: "\x1b[32mSuccess\x1b[0m".to_string(),
            stderr: "\x1b[31mWarning\x1b[0m".to_string(),
            success: true,
            command: "ls -la".into(),
        };
        let preserved = format_output(&infra, ansi_output, true).await.unwrap();
        assert_eq!(
            preserved,
            "<stdout>\x1b[32mSuccess\x1b[0m</stdout>\n<stderr>\x1b[31mWarning\x1b[0m</stderr>"
        );

        // Test with keep_ansi = false (should strip ANSI codes)
        let ansi_output = CommandOutput {
            stdout: "\x1b[32mSuccess\x1b[0m".to_string(),
            stderr: "\x1b[31mWarning\x1b[0m".to_string(),
            success: true,
            command: "ls -la".into(),
        };
        let stripped = format_output(&infra, ansi_output, false).await.unwrap();
        assert_eq!(
            stripped,
            "<stdout>Success</stdout>\n<stderr>Warning</stderr>"
        );
    }

    #[tokio::test]
    async fn test_format_output_with_large_command_output() {
        let infra = Arc::new(MockInfrastructure::new());
        // Test with keep_ansi = true (should preserve ANSI codes)
        let ansi_output = CommandOutput {
            stdout: "\x1b[32mSuccess\x1b[0m".repeat(40_050),
            stderr: "\x1b[31mWarning\x1b[0m".repeat(40_050),
            success: true,
            command: "ls -la".into(),
        };
        let preserved = format_output(&infra, ansi_output, false).await.unwrap();
        insta::assert_snapshot!(preserved);
    }
}
