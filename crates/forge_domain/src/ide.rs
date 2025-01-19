use std::path::PathBuf;

use async_trait::async_trait;

/// Status of the current workspace in the IDE
pub struct Workspace {
    /// ID of the workspace
    pub workspace_id: WorkspaceId,

    /// List of open files in the IDE
    pub opened_files: Vec<PathBuf>,

    /// The file that is currently focused in the IDE
    pub focused_file: PathBuf,
}

#[derive(Debug, derive_more::From)]
pub struct ProcessId(u32);

#[derive(Debug, derive_more::From)]
pub struct WorkspaceId(String);

/// Represents an IDE. Contains meta information about the IDE.
#[derive(Debug)]
pub struct Ide {
    pub name: String,
    pub version: Option<String>,
    pub process: ProcessId,
    pub working_directory: PathBuf,
    pub workspace_id: WorkspaceId,
}

/// Represents functionality for interacting with IDEs
#[async_trait]
pub trait IdeRepository {
    /// List of all the IDEs that are running on the system on the CWD.
    async fn get_active_ides(&self) -> anyhow::Result<Vec<Ide>>;

    /// Get the status of workspace of the provided IDE
    async fn get_workspace(&self, ide: &WorkspaceId) -> anyhow::Result<Workspace>;
}
