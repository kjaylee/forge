use forge_tool_macros::Description as DescriptionDerive;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::{Description, ToolCallService};

#[derive(Deserialize, JsonSchema)]
pub struct FSWriteInput {
    /// The path of the file to write to (relative to the current working
    /// directory)
    pub path: String,
    /// The content to write to the file. ALWAYS provide the COMPLETE intended
    /// content of the file, without any truncation or omissions. You MUST
    /// include ALL parts of the file, even if they haven't been modified.
    pub content: String,
}

/// Request to write content to a file at the specified path. If the file
/// exists, it will be overwritten with the provided content. If the file
/// doesn't exist, it will be created. This tool will automatically create any
/// directories needed to write the file.
#[derive(DescriptionDerive)]
pub struct FSWrite;

#[async_trait::async_trait]
impl ToolCallService for FSWrite {
    type Input = FSWriteInput;
    type Output = FSWriteOutput;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        tokio::fs::write(&input.path, &input.content)
            .await
            .map_err(|e| e.to_string())?;
        Ok(FSWriteOutput { path: input.path, content: input.content })
    }
}

#[derive(Serialize, JsonSchema)]
pub struct FSWriteOutput {
    pub path: String,
    pub content: String,
}

#[cfg(test)]
mod test {
    use crate::fs::tests::Fixture;

    use super::*;

    #[tokio::test]
    async fn test_fs_write_success() {
        let setup = Fixture::setup(|temp_dir| async { temp_dir }).await;
        let output = setup
            .run(
                FSWrite,
                FSWriteInput {
                    path: setup.join("test.txt"),
                    content: "Hello, World!".to_string(),
                },
            )
            .await
            .unwrap();

        assert_eq!(output.content, "Hello, World!");
    }
}
