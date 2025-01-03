use forge_tool_macros::Description as DescriptionDerive;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::{Description, ToolCallService};

#[derive(Deserialize, JsonSchema)]
pub struct FSReadInput {
    /// The path of the file to read (relative to the current working directory)
    pub path: String,
}

/// Request to read the contents of a file at the specified path. Use this when
/// you need to examine the contents of an existing file you do not know the
/// contents of, for example to analyze code, review text files, or extract
/// information from configuration files. Automatically extracts raw text from
/// PDF and DOCX files. May not be suitable for other types of binary files, as
/// it returns the raw content as a string.
#[derive(DescriptionDerive)]
pub struct FSRead;

#[async_trait::async_trait]
impl ToolCallService for FSRead {
    type Input = FSReadInput;
    type Output = String;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let content = tokio::fs::read_to_string(&input.path)
            .await
            .map_err(|e| e.to_string())?;
        Ok(content)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::fs::tests::{File, FixtureBuilder};

    #[tokio::test]
    async fn test_fs_read_success() {
        let content = "Hello, World!";
        let setup = FixtureBuilder::default()
            .files(vec![File::new("test.txt", content)])
            .build()
            .await;
        let result = setup
            .run(FSRead, FSReadInput { path: setup.join("test.txt") })
            .await
            .unwrap();
        assert_eq!(result, content);
    }

    #[tokio::test]
    async fn test_fs_read_nonexistent_file() {
        let setup = FixtureBuilder::default().build().await;
        let result = setup
            .run(FSRead, FSReadInput { path: setup.join("nonexistent.txt") })
            .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_fs_read_empty_file() {
        let setup = FixtureBuilder::default()
            .files(vec![File::new("empty.txt", "")])
            .build()
            .await;
        let result = setup
            .run(FSRead, FSReadInput { path: setup.join("empty.txt") })
            .await
            .unwrap();
        assert_eq!(result, "");
    }

    #[test]
    fn test_description() {
        assert!(FSRead::description().len() > 100)
    }
}
