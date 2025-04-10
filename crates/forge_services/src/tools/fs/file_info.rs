use std::path::Path;

use anyhow::Context;
use forge_domain::{Conversation, ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::tools::utils::assert_absolute_path;

#[derive(Deserialize, JsonSchema)]
pub struct FSFileInfoInput {
    /// The path of the file or directory to inspect (absolute path required)
    pub path: String,
}

/// Request to retrieve detailed metadata about a file or directory at the
/// specified path. Returns comprehensive information including size, creation
/// time, last modified time, permissions, and type. Path must be absolute. Use
/// this when you need to understand file characteristics without reading the
/// actual content.
#[derive(ToolDescription)]
pub struct FSFileInfo;

//FIXME: This tool isn't being used and can be deleted.
impl NamedTool for FSFileInfo {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_info")
    }
}

#[async_trait::async_trait]
impl ExecutableTool for FSFileInfo {
    type Input = FSFileInfoInput;

    async fn call(
        &self,
        input: Self::Input,
        conversation: &Conversation,
    ) -> anyhow::Result<String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        // If the path is valid but doesn't exist, we could check if a relative path
        // from the conversation's CWD would exist
        let file_path = if !path.exists() && !path.is_absolute() {
            // Try to resolve relative to conversation's CWD
            conversation.cwd().join(&input.path)
        } else {
            path.to_path_buf()
        };

        let meta = tokio::fs::metadata(&file_path)
            .await
            .with_context(|| format!("Failed to get metadata for '{}'", file_path.display()))?;
        Ok(format!("{:?}", meta))
    }
}

#[cfg(test)]
mod test {
    use std::path::PathBuf;

    use forge_domain::{ConversationId, Workflow};
    use tokio::fs;

    use super::*;
    use crate::tools::utils::TempDir;

    fn create_test_conversation() -> Conversation {
        let id = ConversationId::generate();
        let workflow = Workflow::default();
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("/tmp"));
        Conversation::new(id, workflow, cwd)
    }

    #[tokio::test]
    async fn test_fs_file_info_on_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "test content").await.unwrap();

        let fs_info = FSFileInfo;
        let conversation = create_test_conversation();

        let result = fs_info
            .call(
                FSFileInfoInput { path: file_path.to_string_lossy().to_string() },
                &conversation,
            )
            .await
            .unwrap();

        assert!(result.contains("FileType"));
        assert!(result.contains("permissions"));
        assert!(result.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_on_directory() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("test_dir");
        fs::create_dir(&dir_path).await.unwrap();

        let fs_info = FSFileInfo;
        let conversation = create_test_conversation();

        let result = fs_info
            .call(
                FSFileInfoInput { path: dir_path.to_string_lossy().to_string() },
                &conversation,
            )
            .await
            .unwrap();

        assert!(result.contains("FileType"));
        assert!(result.contains("permissions"));
        assert!(result.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_nonexistent() {
        let temp_dir = TempDir::new().unwrap();
        let nonexistent_path = temp_dir.path().join("nonexistent");

        let fs_info = FSFileInfo;
        let conversation = create_test_conversation();

        let result = fs_info
            .call(
                FSFileInfoInput { path: nonexistent_path.to_string_lossy().to_string() },
                &conversation,
            )
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_file_info_relative_path() {
        let fs_info = FSFileInfo;
        let conversation = create_test_conversation();

        let result = fs_info
            .call(
                FSFileInfoInput { path: "relative/path.txt".to_string() },
                &conversation,
            )
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Path must be absolute"));
    }
}
