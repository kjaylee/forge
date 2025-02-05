use std::io::{self, Write};

use tokio::io::AsyncReadExt;
use tokio::process::Child;

/// An output stream handler that captures and processes command output
pub struct OutputStream {
    buffer: Vec<u8>,
    writer: Box<dyn Write + Send>,
}

impl OutputStream {
    fn new(writer: Box<dyn Write + Send>) -> Self {
        Self { buffer: Vec::new(), writer }
    }

    /// Process stream data from a reader
    async fn process<T: tokio::io::AsyncRead + Unpin>(
        mut self,
        mut reader: T,
    ) -> Result<String, String> {
        let mut buf = [0; 1024];

        while let Ok(n) = reader.read(&mut buf).await {
            if n == 0 {
                break;
            }
            self.write_all(&buf[..n])
                .map_err(|e| format!("Failed to write to stream: {}", e))?;
        }
        self.into_output()
    }

    /// Convert the captured output to a string, removing ANSI escape codes
    fn into_output(self) -> Result<String, String> {
        String::from_utf8(strip_ansi_escapes::strip(self.buffer))
            .map_err(|e| format!("Failed to convert output to string: {}", e))
    }
}

impl Write for OutputStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.writer.write_all(buf)?;
        self.flush()?;
        self.buffer.extend_from_slice(buf);
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

/// A stream processor that handles command output streams
pub struct CommandStreamer {
    child: Child,
}

impl CommandStreamer {
    pub fn new(child: Child) -> Self {
        Self { child }
    }

    /// Stream and process command output
    pub async fn stream(mut self) -> Result<(String, String, bool), String> {
        // Get stream handles
        let stdout = self
            .child
            .stdout
            .take()
            .ok_or_else(|| "Child process stdout not configured".to_string())?;
        let stderr = self
            .child
            .stderr
            .take()
            .ok_or_else(|| "Child process stderr not configured".to_string())?;

        // Process streams concurrently
        let (stdout, stderr) = tokio::try_join!(
            OutputStream::new(Box::new(io::stdout())).process(stdout),
            OutputStream::new(Box::new(io::stderr())).process(stderr)
        )?;

        // Wait for command completion
        let status = self
            .child
            .wait()
            .await
            .map_err(|e| format!("Failed to wait for command: {}", e))?;

        Ok((stdout, stderr, status.success()))
    }
}
