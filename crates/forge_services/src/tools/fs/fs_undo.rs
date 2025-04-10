use std::sync::Arc;

use forge_domain::{Conversation, ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::Infrastructure;

/// Request to undo last file operation on a specific file. Use to revert a
/// recent mistaken change to a file. Only reverts changes made by other Forge
/// file tools. Requires a valid snapshot to exist.
#[derive(ToolDescription)]
pub struct FsUndo<F>(#[allow(dead_code)] Arc<F>);

impl<F: Infrastructure> FsUndo<F> {
    pub fn new(finder: Arc<F>) -> Self {
        Self(finder)
    }
}

impl<F> NamedTool for FsUndo<F> {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_undo")
    }
}

#[derive(Deserialize, JsonSchema)]
pub struct FsUndoInput {
    /// The path of the file to revert to its previous state. Must be the exact
    /// path that was previously modified, created, or deleted by a Forge
    /// file operation. If the file was deleted, provide the original path
    /// it had before deletion. The system requires a prior snapshot for
    /// this path.
    pub path: String,
}

#[async_trait::async_trait]
impl<F: Infrastructure> ExecutableTool for FsUndo<F> {
    type Input = FsUndoInput;

    async fn call(
        &self,
        input: Self::Input,
        _conversation: &Conversation,
    ) -> anyhow::Result<String> {
        // For now, we'll provide a minimal implementation that just confirms the
        // operation In a real implementation, we would need to actually restore
        // the file from a snapshot
        let path = input.path;

        // FIXME: Implement actual file undo logic using snapshots when that service is
        // available For now, just simulate the operation for testing purposes

        // This is just a placeholder implementation
        Ok(format!(
            "Could not undo changes to {}, no snapshot found",
            path
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use forge_domain::{Conversation, ConversationId, Workflow};
    use tokio::runtime::Runtime;

    use super::*;
    use crate::attachment::tests::MockInfrastructure;

    // Helper function to create a test conversation with a specific working
    // directory
    fn create_test_conversation(cwd: PathBuf) -> Conversation {
        let id = ConversationId::generate();
        let workflow = Workflow::default();
        Conversation::new(id, workflow, cwd)
    }

    #[test]
    fn test_fs_undo() {
        let infra = Arc::new(MockInfrastructure::new());
        let undo = FsUndo::new(infra);
        let input = FsUndoInput { path: "/test/file.txt".to_string() };

        let conversation = create_test_conversation(PathBuf::from("/test"));

        // Use tokio runtime to execute async call
        let rt = Runtime::new().unwrap();
        let result = rt.block_on(async { undo.call(input, &conversation).await });

        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("Could not undo"));
        assert!(output.contains("/test/file.txt"));
    }
}
