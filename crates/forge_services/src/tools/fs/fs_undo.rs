use std::path::Path;
use std::sync::Arc;

use forge_display::TitleFormat;
use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::infra::FsSnapshotService;
use crate::Infrastructure;

/// Reverts the most recent file operation (create/modify/delete) on a specific
/// file. Use this tool when you need to recover from mistaken file changes or
/// undesired modifications. It restores the file to its state before the last
/// operation performed by another tool_forge_fs_* tool. The tool ONLY undoes
/// changes made by Forge tools and can't revert changes made outside Forge or
/// multiple operations at once. Each call undoes only the most recent change
/// for the specified file. Returns a success message on completion or an error
/// if no previous snapshot exists or if the path is invalid.
#[derive(Default, ToolDescription)]
pub struct FsUndo<F>(Arc<F>);

impl<F> FsUndo<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self(infra)
    }
}

impl<F> NamedTool for FsUndo<F> {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_undo")
    }
}

#[derive(Deserialize, JsonSchema)]
pub struct UndoInput {
    /// The absolute path of the file to revert to its previous state. Must be
    /// the exact path that was previously modified, created, or deleted by
    /// a Forge file operation. If the file was deleted, provide the
    /// original path it had before deletion. The system requires a prior
    /// snapshot for this path.
    pub path: String,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for FsUndo<F> {
    type Input = UndoInput;
    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        let path = Path::new(&input.path);
        self.0.file_snapshot_service().undo_snapshot(path).await?;

        // Display a message about the file being read
        let message = TitleFormat::success("Undo").sub_title(path.display().to_string());
        println!("{}", message.format());
        Ok(format!(
            "Successfully undid last operation on path: {}",
            input.path
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tempfile::TempDir;

    use super::*;
    use crate::tools::registry::tests::Stub;

    #[tokio::test]
    async fn test_successful_undo() {
        // Arrange
        let temp_dir = TempDir::new().unwrap();
        let test_path = temp_dir.path().join("success.txt");
        let infra = Arc::new(Stub::default());
        let undo = FsUndo::new(infra);

        // Act
        let result = undo
            .call(UndoInput { path: test_path.to_string_lossy().to_string() })
            .await;

        // Assert
        assert!(result.is_ok(), "Expected successful undo operation");
        assert_eq!(
            result.unwrap(),
            format!(
                "Successfully undid last operation on path: {}",
                test_path.display()
            ),
            "Unexpected success message"
        );
    }

    #[tokio::test]
    async fn test_tool_name() {
        assert_eq!(
            FsUndo::<Stub>::tool_name().as_str(),
            "tool_forge_fs_undo",
            "Tool name should match expected value"
        );
    }
}
