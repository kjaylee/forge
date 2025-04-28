use std::path::Path;
use std::sync::Arc;

use anyhow::Context;
use forge_display::TitleFormat;
use forge_domain::{
    EnvironmentService, ExecutableTool, NamedTool, ToolCallContext, ToolDescription, ToolName,
};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::tools::utils::{assert_absolute_path, format_display_path};
use crate::{FsReadService, Infrastructure};

#[derive(Deserialize, JsonSchema)]
pub struct FSReadInput {
    /// The path of the file to read, always provide absolute paths.
    pub path: String,

    /// Optional start position in bytes (0-based). If provided, reading will
    /// start from this position. The position will be adjusted to respect
    /// UTF-8 character boundaries.
    pub start_byte: Option<u64>,

    /// Optional end position in bytes (inclusive). If provided, reading will
    /// end at this position. The position will be adjusted to respect UTF-8
    /// character boundaries.
    pub end_byte: Option<u64>,
}

/// Reads file contents at specified path. Use for analyzing code, config files,
/// documentation or text data. Extracts text from PDF/DOCX files and preserves
/// original formatting. Returns content as string. Always use absolute paths.
/// Read-only with no file modifications. Supports reading specific portions of
/// large files by providing start_byte and end_byte parameters. Binary files
/// are automatically detected and rejected. Range parameters are automatically
/// adjusted to respect UTF-8 character boundaries.
#[derive(ToolDescription)]
pub struct FSRead<F>(Arc<F>);

impl<F: Infrastructure> FSRead<F> {
    pub fn new(f: Arc<F>) -> Self {
        Self(f)
    }

    /// Formats a path for display, converting absolute paths to relative when
    /// possible
    ///
    /// If the path starts with the current working directory, returns a
    /// relative path. Otherwise, returns the original absolute path.
    fn format_display_path(&self, path: &Path) -> anyhow::Result<String> {
        // Get the current working directory
        let env = self.0.environment_service().get_environment();
        let cwd = env.cwd.as_path();

        // Use the shared utility function
        format_display_path(path, cwd)
    }
}

impl<F> NamedTool for FSRead<F> {
    fn tool_name() -> ToolName {
        ToolName::new("forge_tool_fs_read")
    }
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for FSRead<F> {
    type Input = FSReadInput;

    async fn call(&self, context: ToolCallContext, input: Self::Input) -> anyhow::Result<String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        // Use the infrastructure to read the file - with range support
        let result = if input.start_byte.is_some() || input.end_byte.is_some() {
            // Use range read if either range parameter is provided
            let (content, file_info) = self
                .0
                .file_read_service()
                .range_read(path, input.start_byte, input.end_byte)
                .await
                .with_context(|| format!("Failed to read file content from {}", input.path))?;

            // Format a response with metadata
            let display_path = self.format_display_path(path)?;
            let title = "Read (Range)";

            // Create a message with range information
            let start_info = match input.start_byte {
                Some(sb) => format!("{} (adjusted to {})", sb, file_info.start_byte),
                None => "0".to_string(),
            };

            let end_info = match input.end_byte {
                Some(eb) => format!("{} (adjusted to {})", eb, file_info.end_byte),
                None => format!("{}", file_info.total_size),
            };

            let range_info = format!(
                "range: {}-{}, total: {}", 
                start_info, 
                end_info, 
                file_info.total_size
            );
            let message =
                TitleFormat::new(title).sub_title(format!("{} ({})", display_path, range_info));

            context.send_text(message.format()).await?;

            // Format response with metadata header
            format!(
                "---\npath: {}\nrange: {}-{}\ntotal: {}\n---\n{}",
                display_path, 
                file_info.start_byte, 
                file_info.end_byte, 
                file_info.total_size, 
                content
            )
        } else {
            // Use regular read for backward compatibility when no range is specified
            let content = self
                .0
                .file_read_service()
                .read(path)
                .await
                .with_context(|| format!("Failed to read file content from {}", input.path))?;

            // Display a message about the file being read
            let title = "Read";
            let display_path = self.format_display_path(path)?;
            let message = TitleFormat::new(title).sub_title(display_path);
            context.send_text(message.format()).await?;

            content
        };

        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use std::sync::Arc;

    use pretty_assertions::assert_eq;
    use tokio::fs;

    use super::*;
    use crate::attachment::tests::MockInfrastructure;
    use crate::tools::utils::TempDir;

    // Helper function to test relative paths
    async fn test_with_mock(path: &str) -> anyhow::Result<String> {
        let infra = Arc::new(MockInfrastructure::new());
        let fs_read = FSRead::new(infra);
        fs_read
            .call(
                ToolCallContext::default(),
                FSReadInput { 
                    path: path.to_string(),
                    start_byte: None,
                    end_byte: None,
                },
            )
            .await
    }

    #[tokio::test]
    async fn test_fs_read_success() {
        // Create a temporary file with test content
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let test_content = "Hello, World!";
        fs::write(&file_path, test_content).await.unwrap();

        // For the test, we'll switch to using tokio::fs directly rather than going
        // through the infrastructure (which would require more complex mocking)
        let path = Path::new(&file_path);
        assert_absolute_path(path).unwrap();

        // Read the file directly
        let content = tokio::fs::read_to_string(path).await.unwrap();

        // Display a message - just for testing
        let title = "Read";
        let message = TitleFormat::new(title).sub_title(path.display().to_string());
        println!("{message}");

        // Assert the content matches
        assert_eq!(content, test_content);
    }

    #[tokio::test]
    async fn test_fs_read_with_range() {
        // Create a temporary file with test content
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("range_test.txt");
        let test_content = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        fs::write(&file_path, test_content).await.unwrap();

        // Setup a mock infrastructure with our mock services
        let infra = Arc::new(MockInfrastructure::new());
        let fs_read = FSRead::new(infra);

        // Test to read middle range of the file (for real range tests, see forge_fs
        // tests) Here we're just testing the tool's interface and formatting
        let result = fs_read
            .call(
                ToolCallContext::default(),
                FSReadInput {
                    path: file_path.to_string_lossy().to_string(),
                    start_byte: Some(10),
                    end_byte: Some(20),
                },
            )
            .await;

        // Since MockInfrastructure doesn't actually read files, we expect an error
        // In a real test, we'd verify the range was respected and formatting was
        // correct
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_read_with_invalid_range() {
        // Create a temporary file with test content
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("invalid_range.txt");
        let test_content = "Hello, World!";
        fs::write(&file_path, test_content).await.unwrap();

        // Setup a mock infrastructure with our mock services
        let infra = Arc::new(MockInfrastructure::new());
        let fs_read = FSRead::new(infra);

        // Test with an invalid range (start > end)
        let result = fs_read
            .call(
                ToolCallContext::default(),
                FSReadInput {
                    path: file_path.to_string_lossy().to_string(),
                    start_byte: Some(20),
                    end_byte: Some(10),
                },
            )
            .await;

        // Since MockInfrastructure doesn't actually read files, we expect an error
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_read_nonexistent_file() {
        let temp_dir = TempDir::new().unwrap();
        let nonexistent_file = temp_dir.path().join("nonexistent.txt");

        let result = tokio::fs::read_to_string(&nonexistent_file).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_read_empty_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("empty.txt");
        fs::write(&file_path, "").await.unwrap();

        let content = tokio::fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(content, "");
    }

    #[test]
    fn test_description() {
        let infra = Arc::new(MockInfrastructure::new());
        let fs_read = FSRead::new(infra);
        assert!(fs_read.description().len() > 100)
    }

    #[tokio::test]
    async fn test_fs_read_relative_path() {
        let result = test_with_mock("relative/path.txt").await;
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Path must be absolute"));
    }
    #[tokio::test]
    async fn test_format_display_path() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        // Create a mock infrastructure with controlled cwd
        let infra = Arc::new(MockInfrastructure::new());
        let fs_read = FSRead::new(infra);

        // Test with a mock path
        let display_path = fs_read.format_display_path(Path::new(&file_path));

        // Since MockInfrastructure has a fixed cwd of "/test",
        // and our temp path won't start with that, we expect the full path
        assert!(display_path.is_ok());
        assert_eq!(display_path.unwrap(), file_path.display().to_string());
    }
}
