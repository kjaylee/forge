use std::io::{self, Write};
use std::path::PathBuf;

use tokio::io::AsyncRead;
use tokio::process::Command;

/// A command executor that handles command creation and execution
#[derive(Debug)]
pub struct CommandExecutor {
    command: Command,
    colored: bool,
}

pub struct Output {
    pub stdout: String,
    pub stderr: String,
    pub success: bool,
}

impl CommandExecutor {
    /// Create a new command executor with the specified command and working
    /// directory
    pub fn new(command: &str, cwd: &PathBuf) -> Self {
        let mut command = if cfg!(target_os = "windows") {
            let mut c = Command::new("cmd");
            c.args(["/C", command]);
            c
        } else {
            let mut c = Command::new("sh");
            c.args(["-c", command]);
            c
        };
        // Set the current working directory for the command
        command.current_dir(cwd);
        // Kill the command when the handler is dropped
        command.kill_on_drop(true);
        Self { command, colored: false }
    }

    /// Enable colored output for the command
    pub fn colored(mut self) -> Self {
        self.command.env("CLICOLOR_FORCE", "1");
        self.colored = true;
        self
    }

    /// executes the command and streams the output of command to stdout and
    /// stderr.
    pub async fn execute(mut self) -> anyhow::Result<Output> {
        // don't change this configuration else it will break the cli output.
        self.command
            .stdin(std::process::Stdio::inherit())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());

        let mut child = self.command.spawn()?;

        let mut stdout_pipe = child.stdout.take();
        let mut stderr_pipe = child.stderr.take();

        let stdout_fut = stream(&mut stdout_pipe, io::stdout());
        let stderr_fut = stream(&mut stderr_pipe, io::stderr());

        let (status, stdout, stderr) = tokio::try_join!(child.wait(), stdout_fut, stderr_fut)?;
        // Drop happens after `try_join` due to <https://github.com/tokio-rs/tokio/issues/4309>
        drop(stdout_pipe);
        drop(stderr_pipe);

        let (stdout, stderr) = if self.colored {
            (
                String::from_utf8(strip_ansi_escapes::strip(stdout))?,
                String::from_utf8(strip_ansi_escapes::strip(stderr))?,
            )
        } else {
            (String::from_utf8(stdout)?, String::from_utf8(stderr)?)
        };

        Ok(Output { success: status.success(), stdout, stderr })
    }
}

// streams the output from child process to stdout and stderr.
async fn stream<A: AsyncRead + Unpin, W: Write>(
    io: &mut Option<A>,
    mut writer: W,
) -> io::Result<Vec<u8>> {
    let mut output = Vec::new();
    use tokio::io::AsyncReadExt;
    if let Some(io) = io.as_mut() {
        let mut buff = [0; 1024];
        loop {
            let n = io.read(&mut buff).await?;
            if n == 0 {
                break;
            }
            writer.write_all(&buff[..n])?;
            writer.flush()?;
            output.extend_from_slice(&buff[..n]);
        }
    }
    Ok(output)
}
