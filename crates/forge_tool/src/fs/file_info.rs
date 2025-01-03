use forge_tool_macros::Description as DescriptionDerive;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{Description, ToolCallService};

#[derive(Deserialize, JsonSchema, Serialize, Clone)]
pub struct FSFileInfoInput {
    /// The path of the file or directory to inspect (relative to the current
    /// working directory)
    #[serde(rename = "@path")]
    pub path: String,
}

/// Request to retrieve detailed metadata about a file or directory at the
/// specified path. Returns comprehensive information including size, creation
/// time, last modified time, permissions, and type. Use this when you need to
/// understand file characteristics without reading the actual content.
#[derive(DescriptionDerive)]
pub struct FSFileInfo;

#[derive(Serialize, JsonSchema)]
#[serde(rename = "fs_file_info")]
pub struct FSFileInfoOutput {
    #[serde(flatten)]
    args: FSFileInfoInput,
    #[serde(rename = "$value")]
    pub metadata: String,
}

#[async_trait::async_trait]
impl ToolCallService for FSFileInfo {
    type Input = FSFileInfoInput;
    type Output = FSFileInfoOutput;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let meta = tokio::fs::metadata(&input.path)
            .await
            .map_err(|e| e.to_string())?;
        Ok(FSFileInfoOutput { args: input.clone(), metadata: format!("{:?}", meta) })
    }
}

#[cfg(test)]
mod test {
    use tempfile::TempDir;
    use tokio::fs;

    use super::*;

    #[tokio::test]
    async fn test_fs_file_info_on_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "test content").await.unwrap();

        let fs_info = FSFileInfo;
        let result = fs_info
            .call(FSFileInfoInput { path: file_path.to_string_lossy().to_string() })
            .await
            .unwrap();

        assert!(result.metadata.contains("FileType"));
        assert!(result.metadata.contains("permissions"));
        assert!(result.metadata.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_on_directory() {
        let temp_dir = TempDir::new().unwrap();
        let dir_path = temp_dir.path().join("test_dir");
        fs::create_dir(&dir_path).await.unwrap();

        let fs_info = FSFileInfo;
        let result = fs_info
            .call(FSFileInfoInput { path: dir_path.to_string_lossy().to_string() })
            .await
            .unwrap();

        assert!(result.metadata.contains("FileType"));
        assert!(result.metadata.contains("permissions"));
        assert!(result.metadata.contains("modified"));
    }

    #[tokio::test]
    async fn test_fs_file_info_nonexistent() {
        let temp_dir = TempDir::new().unwrap();
        let nonexistent_path = temp_dir.path().join("nonexistent");

        let fs_info = FSFileInfo;
        let result = fs_info
            .call(FSFileInfoInput { path: nonexistent_path.to_string_lossy().to_string() })
            .await;

        assert!(result.is_err());
    }

    #[test]
    fn serialize_to_xml() {
        let output = FSFileInfoOutput {
            args: FSFileInfoInput { path: ".".to_string() },
            metadata: "metadata".to_string(),
        };
        let mut buffer = Vec::new();
        let mut writer = quick_xml::Writer::new_with_indent(&mut buffer, b' ', 4);
        writer.write_serializable("fs_file_info", &output).unwrap();
        insta::assert_snapshot!(std::str::from_utf8(&buffer).unwrap());
    }
}
