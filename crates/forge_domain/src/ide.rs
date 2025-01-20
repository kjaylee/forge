use std::path::PathBuf;

use async_trait::async_trait;

/// Status of the current workspace in the IDE
#[derive(Debug, Default, derive_setters::Setters)]
pub struct Workspace {
    /// ID of the workspace
    pub workspace_id: WorkspaceId,

    /// List of open files in the IDE
    pub opened_files: Vec<PathBuf>,

    /// The file that is currently focused in the IDE
    pub focused_file: PathBuf,
}

impl Workspace {
    pub fn opened_files_xml(&self, ide: &str) -> String {
        self.opened_files
            .iter()
            .map(|f| f.to_string_lossy())
            .map(|v| Self::enclose_in_xml_tag(ide, v.as_ref()))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn enclose_in_xml_tag(ide: &str, value: &str) -> String {
        let tag = match ide {
            "VS Code" => "vs_code_active_file",
            _ => "",
        };
        format!("<{}>{}</{}>", tag, value, tag)
    }

    pub fn focused_file_xml(&self, ide: &str) -> String {
        Self::enclose_in_xml_tag(ide, self.focused_file.to_string_lossy().as_ref())
    }
}

#[derive(Debug, derive_more::From)]
pub struct ProcessId(u32);

impl ProcessId {
    pub fn as_u32(&self) -> u32 {
        self.0
    }
}

#[derive(Debug, Default, Clone, derive_more::From)]
pub struct WorkspaceId(String);

impl WorkspaceId {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

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
