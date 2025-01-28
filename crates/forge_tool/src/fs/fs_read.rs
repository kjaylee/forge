use std::path::Path;

use forge_domain::{NamedTool, TokenCounter, ToolCallService, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use super::fs_find;
use crate::utils::assert_absolute_path;

#[derive(Deserialize, JsonSchema)]
pub struct FSReadInput {
    /// The path of the file to read, always provide absolute paths.
    pub path: String,
}

/// Request to read the contents of a file at the specified path. Use this when
/// you need to examine the contents of an existing file you do not know the
/// contents of, for example to analyze code, review text files, or extract
/// information from configuration files. Automatically extracts raw text from
/// PDF and DOCX files. May not be suitable for other types of binary files, as
/// it returns the raw content as a string.
#[derive(Default, ToolDescription)]
pub struct FSRead {
    token_counter: TokenCounter,
}

impl NamedTool for FSRead {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_read")
    }
}

#[async_trait::async_trait]
impl ToolCallService for FSRead {
    type Input = FSReadInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;
        let out = tokio::fs::read_to_string(path)
            .await
            .map_err(|e| format!("Failed to read file content from {}: {}", input.path, e));

        match out {
            Ok(output) => Ok(process_output(self.token_counter.clone(), output)),
            Err(output) => Err(process_output(self.token_counter.clone(), output)),
        }
    }
}

fn process_output(token_counter: TokenCounter, output: String) -> String {
    let token_count = token_counter.count_tokens(&output);
    if token_count > TokenCounter::MAX_TOOL_OUTPUT_TOKENS {
        return format!(
            "Output exceeds token limit ({} > {}), use {} to find relevant information",
            token_count,
            TokenCounter::MAX_TOOL_OUTPUT_TOKENS,
            fs_find::FSSearch::tool_name().as_str()
        );
    }
    output
}

#[cfg(test)]
mod test {
    use pretty_assertions::assert_eq;
    use tokio::fs;

    use super::*;
    use crate::utils::TempDir;

    #[tokio::test]
    async fn test_fs_read_success() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        let test_content = "Hello, World!";
        fs::write(&file_path, test_content).await.unwrap();

        let fs_read = FSRead::default();
        let result = fs_read
            .call(FSReadInput { path: file_path.to_string_lossy().to_string() })
            .await
            .unwrap();

        assert_eq!(result, test_content);
    }

    #[tokio::test]
    async fn test_fs_read_nonexistent_file() {
        let temp_dir = TempDir::new().unwrap();
        let nonexistent_file = temp_dir.path().join("nonexistent.txt");

        let fs_read = FSRead::default();
        let result = fs_read
            .call(FSReadInput { path: nonexistent_file.to_string_lossy().to_string() })
            .await;

        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_read_empty_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("empty.txt");
        fs::write(&file_path, "").await.unwrap();

        let fs_read = FSRead::default();
        let result = fs_read
            .call(FSReadInput { path: file_path.to_string_lossy().to_string() })
            .await
            .unwrap();

        assert_eq!(result, "");
    }

    #[test]
    fn test_description() {
        assert!(FSRead::default().description().len() > 100)
    }

    #[tokio::test]
    async fn test_fs_read_relative_path() {
        let fs_read = FSRead::default();
        let result = fs_read
            .call(FSReadInput { path: "relative/path.txt".to_string() })
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Path must be absolute"));
    }
}
