use std::path::Path;
use std::sync::Arc;

use forge_domain::{Conversation, ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::tools::utils::assert_absolute_path;
use crate::{FileRemoveService, FsMetaService, Infrastructure};

#[derive(Deserialize, JsonSchema)]
pub struct FSRemoveInput {
    /// The path of the file to remove (absolute path required)
    pub path: String,
}

/// Request to remove a file at the specified path. Use this when you need to
/// delete an existing file. The path must be absolute. This operation cannot
/// be undone, so use it carefully.
#[derive(ToolDescription)]
pub struct FSRemove<T>(Arc<T>);

impl<T: Infrastructure> FSRemove<T> {
    pub fn new(infra: Arc<T>) -> Self {
        Self(infra)
    }
}

impl<T> NamedTool for FSRemove<T> {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_remove")
    }
}

#[async_trait::async_trait]
impl<T: Infrastructure> ExecutableTool for FSRemove<T> {
    type Input = FSRemoveInput;

    async fn call(
        &self,
        input: Self::Input,
        conversation: &Conversation,
    ) -> anyhow::Result<String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        // Try to convert relative path to absolute using the conversation's CWD
        let file_path = if !path.exists() && !path.is_absolute() {
            conversation.cwd().join(&input.path)
        } else {
            path.to_path_buf()
        };

        // Check if the file exists
        if !self.0.file_meta_service().exists(&file_path).await? {
            return Err(anyhow::anyhow!("File not found: {}", file_path.display()));
        }

        // Check if it's a file
        if !self.0.file_meta_service().is_file(&file_path).await? {
            return Err(anyhow::anyhow!(
                "Path is not a file: {}",
                file_path.display()
            ));
        }

        // Remove the file
        self.0.file_remove_service().remove(&file_path).await?;

        Ok(format!(
            "Successfully removed file: {}",
            file_path.display()
        ))
    }
}

#[cfg(test)]
mod test {
    use std::path::PathBuf;

    use bytes::Bytes;
    use forge_domain::{ConversationId, Workflow};

    use super::*;
    use crate::attachment::tests::MockInfrastructure;
    use crate::tools::utils::TempDir;
    use crate::{FsCreateDirsService, FsWriteService};

    fn create_test_conversation() -> Conversation {
        let id = ConversationId::generate();
        let workflow = Workflow::default();
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("/tmp"));
        Conversation::new(id, workflow, cwd)
    }

    #[tokio::test]
    async fn test_fs_remove_success() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let infra = Arc::new(MockInfrastructure::new());
        let conversation = create_test_conversation();

        // Create a test file
        infra
            .file_write_service()
            .write(
                file_path.as_path(),
                Bytes::from("test content".as_bytes().to_vec()),
            )
            .await
            .unwrap();

        assert!(infra.file_meta_service().exists(&file_path).await.unwrap());

        let fs_remove = FSRemove::new(infra.clone());
        let result = fs_remove
            .call(
                FSRemoveInput { path: file_path.to_string_lossy().to_string() },
                &conversation,
            )
            .await
            .unwrap();

        assert!(result.contains("Successfully removed file"));
        assert!(!infra.file_meta_service().exists(&file_path).await.unwrap());
    }

    #[tokio::test]
    async fn test_fs_remove_nonexistent_file() {
        let temp_dir = TempDir::new().unwrap();
        let nonexistent_file = temp_dir.path().join("nonexistent.txt");
        let infra = Arc::new(MockInfrastructure::new());
        let conversation = create_test_conversation();

        let fs_remove = FSRemove::new(infra);
        let result = fs_remove
            .call(
                FSRemoveInput { path: nonexistent_file.to_string_lossy().to_string() },
                &conversation,
            )
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("File not found"));
    }

    #[tokio::test]
    async fn test_fs_remove_directory() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("test_dir");
        let infra = Arc::new(MockInfrastructure::new());
        let conversation = create_test_conversation();

        // Create a test directory
        infra
            .create_dirs_service()
            .create_dirs(dir_path.as_path())
            .await
            .unwrap();
        assert!(infra
            .file_meta_service()
            .exists(dir_path.as_path())
            .await
            .unwrap());

        let fs_remove = FSRemove::new(infra.clone());
        let result = fs_remove
            .call(
                FSRemoveInput { path: dir_path.to_string_lossy().to_string() },
                &conversation,
            )
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Path is not a file"));
        assert!(infra
            .file_meta_service()
            .exists(dir_path.as_path())
            .await
            .unwrap());
    }

    #[tokio::test]
    async fn test_fs_remove_relative_path() {
        let infra = Arc::new(MockInfrastructure::new());
        let conversation = create_test_conversation();

        let fs_remove = FSRemove::new(infra);
        let result = fs_remove
            .call(
                FSRemoveInput { path: "relative/path.txt".to_string() },
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
