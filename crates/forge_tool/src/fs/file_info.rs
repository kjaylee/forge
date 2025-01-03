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
    use super::*;
    use crate::fs::tests::{File, FixtureBuilder};

    #[tokio::test]
    async fn test_fs_file_info_on_file() {
        let setup = FixtureBuilder::default()
            .files(vec![File::new("test.txt", "test-content")])
            .build()
            .await;
        let result = setup
            .run(FSFileInfo, FSFileInfoInput { path: setup.join("test.txt") })
            .await
            .unwrap();

        // Verify the debug output contains expected metadata fields
        assert!(result.contains("FileType"));
        assert!(result.contains("permissions"));
        assert!(result.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_on_directory() {
        let setup = FixtureBuilder::default()
            .dirs(vec![String::from("test_dir")])
            .build()
            .await;

        let result = setup
            .run(FSFileInfo, FSFileInfoInput { path: setup.join("test_dir") })
            .await
            .unwrap();
        assert!(result.contains("FileType"));
        assert!(result.contains("permissions"));
        assert!(result.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_nonexistent() {
        let setup = FixtureBuilder::default().build().await;
        let result = setup
            .run(
                FSFileInfo,
                FSFileInfoInput { path: setup.join("nonexistent.txt") },
            )
            .await;
        assert!(result.is_err());
    }
}
