use forge_tool_macros::Description as DescriptionDerive;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::{Description, ToolCallService};

#[derive(Deserialize, JsonSchema)]
pub struct FSFileInfoInput {
    /// The path of the file or directory to inspect (relative to the current
    /// working directory)
    pub path: String,
}

/// Request to retrieve detailed metadata about a file or directory at the
/// specified path. Returns comprehensive information including size, creation
/// time, last modified time, permissions, and type. Use this when you need to
/// understand file characteristics without reading the actual content.
#[derive(DescriptionDerive)]
pub struct FSFileInfo;

#[async_trait::async_trait]
impl ToolCallService for FSFileInfo {
    type Input = FSFileInfoInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let meta = tokio::fs::metadata(input.path)
            .await
            .map_err(|e| e.to_string())?;
        Ok(format!("{:?}", meta))
    }
}

#[cfg(test)]
mod test {
    use std::path::PathBuf;

    use tempfile::TempDir;
    use tokio::fs;

    use super::*;

    struct Fixture {
        path: PathBuf,
        // Keep temp_dir alive for the duration of the test
        _temp_dir: TempDir,
    }

    impl Fixture {
        async fn setup<F, Fut>(creator: F) -> Self
        where
            F: Fn(TempDir) -> Fut,
            Fut: std::future::Future<Output = (PathBuf, TempDir)>,
        {
            let temp_dir = TempDir::new().unwrap();
            let (path, temp_dir) = creator(temp_dir).await;
            Self { path, _temp_dir: temp_dir }
        }

        async fn run(self) -> Result<String, String> {
            let fs_info = FSFileInfo;
            let result = fs_info
                .call(FSFileInfoInput { path: self.path.to_string_lossy().to_string() })
                .await;
            result
        }
    }

    #[tokio::test]
    async fn test_fs_file_info_on_file() {
        let result = Fixture::setup(|temp_dir| async {
            let file_path = temp_dir.path().join("test.txt");
            fs::write(&file_path, "test content").await.unwrap();
            (file_path, temp_dir)
        })
        .await
        .run()
        .await
        .unwrap();

        // Verify the debug output contains expected metadata fields
        assert!(result.contains("FileType"));
        assert!(result.contains("permissions"));
        assert!(result.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_on_directory() {
        let result = Fixture::setup(|temp_dir| async {
            let dir_path = temp_dir.path().join("test_dir");
            fs::create_dir(&dir_path).await.unwrap();
            (dir_path, temp_dir)
        })
        .await
        .run()
        .await
        .unwrap();

        assert!(result.contains("FileType"));
        assert!(result.contains("permissions"));
        assert!(result.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_nonexistent() {
        let result = Fixture::setup(|temp_dir| async {
            let nonexistent_path = temp_dir.path().join("nonexistent");
            (nonexistent_path, temp_dir)
        })
        .await
        .run()
        .await;
        assert!(result.is_err());
    }
}
