use std::path::Path;

use anyhow::Context;
use forge_display::{DiffFormat, VsCodeDiffConfig};
use forge_display::vscode_diff::create_streaming_diff_viewer;
use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::tools::syn;
use crate::tools::utils::assert_absolute_path;

#[derive(Deserialize, JsonSchema)]
pub struct FSWriteInput {
    /// The path of the file to write to (absolute path required)
    pub path: String,
    /// The content to write to the file. ALWAYS provide the COMPLETE intended
    /// content of the file, without any truncation or omissions. You MUST
    /// include ALL parts of the file, even if they haven't been modified.
    pub content: String,
}

/// File System Write Tool
///
/// Creates a new file at the specified path with the provided content.
/// 
/// # Description
/// 
/// This tool allows creating or overwriting files at absolute paths. It:
/// - Requires absolute paths for file locations
/// - Creates any missing intermediary directories automatically
/// - Validates syntax for supported file types
/// - Shows diff between old and new content in terminal and VS Code
/// 
/// # Important
/// 
/// DO NOT attempt to use this tool to move or rename files, use the shell tool instead.
#[derive(ToolDescription)]
pub struct FSWrite;

impl NamedTool for FSWrite {
    /// Returns the name of the tool as a ToolName
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_create")
    }
}

#[async_trait::async_trait]
impl ExecutableTool for FSWrite {
    type Input = FSWriteInput;

    /// Creates a file at the specified path with the provided content.
    /// 
    /// # Parameters
    /// 
    /// * `input` - Contains the path and content for the file to be created
    /// 
    /// # Returns
    /// 
    /// * `Ok(String)` - Success message with bytes written and path
    /// * `Err(anyhow::Error)` - If file creation fails for any reason
    /// 
    /// # Notes
    /// 
    /// This implementation:
    /// - Creates parent directories automatically if they don't exist
    /// - Validates syntax for supported languages (Rust, JavaScript, TypeScript, etc.)
    /// - Shows both terminal and VS Code diff visualization of changes
    /// - Supports animated diffs for better change visualization
    /// - Displays appropriate warnings for syntax issues
    /// - Requires absolute paths for security and clarity
    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        // Validate absolute path requirement
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        // Validate file content if it's a supported language file
        let syntax_warning = syn::validate(&input.path, &input.content);

        // Create parent directories if they don't exist
        if let Some(parent) = Path::new(&input.path).parent() {
            tokio::fs::create_dir_all(parent)
                .await
                .with_context(|| format!("Failed to create directories: {}", input.path))?;
        }

        // record the file content before they're modified
        let old_content = if path.is_file() {
            // if file already exists, we should be able to read it.
            tokio::fs::read_to_string(path).await?
        } else {
            // if file doesn't exist, we should record it as an empty string.
            "".to_string()
        };

        // Write file only after validation passes and directories are created
        tokio::fs::write(&input.path, &input.content).await?;

        let mut result = format!(
            "Successfully wrote {} bytes to {}",
            input.content.len(),
            input.path
        );
        if let Some(warning) = syntax_warning {
            result.push_str("\nWarning: ");
            result.push_str(&warning.to_string());
        }

        // Initialize VS Code diff viewer for streaming updates with animation
        let vscode_config = VsCodeDiffConfig {
            animated_diff: true,          // Enable animated diff
            animation_delay_ms: 80,       // Slightly faster animation for better user experience
            update_frequency_ms: 50,      // More responsive updates
            min_change_percent: 0.1,      // More sensitive to changes
            ..VsCodeDiffConfig::default()
        };
        let mut vs_diff_viewer = match create_streaming_diff_viewer(path, &old_content, vscode_config).await {
            Ok(viewer) => Some(viewer),
            Err(e) => {
                eprintln!("Warning: Failed to create streaming VS Code diff viewer: {}", e);
                None
            }
        };
        
        // Read the modified file content
        let new_content = tokio::fs::read_to_string(path).await?;
        
        // Stream diff line by line to the terminal
        DiffFormat::stream(path.to_path_buf(), &old_content, &new_content, |line| {
            // Update VS Code diff viewer for each line of terminal output
            if let Some(viewer) = &mut vs_diff_viewer {
                if let Err(e) = tokio::task::block_in_place(|| {
                    tokio::runtime::Handle::current().block_on(async {
                        viewer.update(&new_content).await
                    })
                }) {
                    eprintln!("Warning: Failed to update VS Code diff: {}", e);
                }
            }
            
            // Print the line to terminal
            println!("{}", line);
        });
        
        // Finalize the VS Code diff view
        if let Some(mut viewer) = vs_diff_viewer {
            if let Err(e) = viewer.finalize(&new_content).await {
                eprintln!("Warning: Failed to finalize VS Code diff: {}", e);
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use pretty_assertions::assert_eq;
    use tokio::fs;

    use super::*;
    use crate::tools::utils::TempDir;

    /// Asserts that a path exists in the filesystem.
    /// 
    /// # Parameters
    /// 
    /// * `path` - The path to check for existence
    /// 
    /// # Panics
    /// 
    /// If the path does not exist
    async fn assert_path_exists(path: impl AsRef<Path>) {
        assert!(fs::metadata(path).await.is_ok(), "Path should exist");
    }

    #[tokio::test]
    async fn test_fs_write_success() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello, World!";

        let fs_write = FSWrite;
        let output = fs_write
            .call(FSWriteInput {
                path: file_path.to_string_lossy().to_string(),
                content: content.to_string(),
            })
            .await
            .unwrap();

        assert!(output.contains("Successfully wrote"));
        assert!(output.contains(&file_path.display().to_string()));
        assert!(output.contains(&content.len().to_string()));

        // Verify file was actually written
        let content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(content, "Hello, World!")
    }

    #[tokio::test]
    async fn test_fs_write_invalid_rust() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.rs");

        let fs_write = FSWrite;
        let result = fs_write
            .call(FSWriteInput {
                path: file_path.to_string_lossy().to_string(),
                content: "fn main() { let x = ".to_string(),
            })
            .await;

        let output = result.unwrap();
        assert!(output.contains("Warning:"));
    }

    #[tokio::test]
    async fn test_fs_write_valid_rust() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.rs");

        let fs_write = FSWrite;
        let content = "fn main() { let x = 42; }";
        let result = fs_write
            .call(FSWriteInput {
                path: file_path.to_string_lossy().to_string(),
                content: content.to_string(),
            })
            .await;

        let output = result.unwrap();
        assert!(output.contains("Successfully wrote"));
        assert!(output.contains(&file_path.display().to_string()));
        assert!(output.contains(&content.len().to_string()));
        assert!(!output.contains("Warning:"));
        // Verify file contains valid Rust code
        let content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(content, "fn main() { let x = 42; }");
    }

    #[tokio::test]
    async fn test_fs_write_single_directory_creation() {
        let temp_dir = TempDir::new().unwrap();
        let nested_path = temp_dir.path().join("new_dir").join("test.txt");
        let content = "Hello from nested file!";

        let fs_write = FSWrite;
        let result = fs_write
            .call(FSWriteInput {
                path: nested_path.to_string_lossy().to_string(),
                content: content.to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully wrote"));
        // Verify both directory and file were created
        assert_path_exists(&nested_path).await;
        assert_path_exists(nested_path.parent().unwrap()).await;

        // Verify content
        let written_content = fs::read_to_string(&nested_path).await.unwrap();
        assert_eq!(written_content, content);
    }

    #[tokio::test]
    async fn test_fs_write_deep_directory_creation() {
        let temp_dir = TempDir::new().unwrap();
        let deep_path = temp_dir
            .path()
            .join("level1")
            .join("level2")
            .join("level3")
            .join("deep.txt");
        let content = "Deep in the directory structure";

        let fs_write = FSWrite;
        let result = fs_write
            .call(FSWriteInput {
                path: deep_path.to_string_lossy().to_string(),
                content: content.to_string(),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully wrote"));

        // Verify entire path was created
        assert_path_exists(&deep_path).await;
        let mut current = deep_path.parent().unwrap();
        while current != temp_dir.path() {
            assert_path_exists(current).await;
            current = current.parent().unwrap();
        }

        // Verify content
        let written_content = fs::read_to_string(&deep_path).await.unwrap();
        assert_eq!(written_content, content);
    }

    #[tokio::test]
    async fn test_fs_write_with_different_separators() {
        let temp_dir = TempDir::new().unwrap();

        // Use forward slashes regardless of platform
        let path_str = format!("{}/dir_a/dir_b/file.txt", temp_dir.path().to_string_lossy());
        let content = "Testing path separators";

        let fs_write = FSWrite;
        let result = fs_write
            .call(FSWriteInput { path: path_str, content: content.to_string() })
            .await
            .unwrap();

        assert!(result.contains("Successfully wrote"));

        // Convert to platform path and verify
        let platform_path = Path::new(&temp_dir.path())
            .join("dir_a")
            .join("dir_b")
            .join("file.txt");

        assert_path_exists(&platform_path).await;

        // Verify content
        let written_content = fs::read_to_string(&platform_path).await.unwrap();
        assert_eq!(written_content, content);
    }

    #[tokio::test]
    async fn test_fs_write_relative_path() {
        let fs_write = FSWrite;
        let result = fs_write
            .call(FSWriteInput {
                path: "relative/path/file.txt".to_string(),
                content: "test content".to_string(),
            })
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Path must be absolute"));
    }
}
