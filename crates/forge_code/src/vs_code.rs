use std::collections::HashSet;
use std::path::{Path, PathBuf};

use forge_domain::{Ide, IdeRepository, Workspace, WorkspaceId};
use forge_walker::Walker;
use rusqlite::{Connection, OptionalExtension};
use serde_json::Value;

use crate::platform::Platforms;

pub struct Code {
    cwd: String,
    code_info: Platforms,
}

#[async_trait::async_trait]
impl IdeRepository for Code {
    async fn get_active_ides(&self) -> anyhow::Result<Vec<Ide>> {
        todo!()
    }

    async fn get_workspace(&self, ide: &WorkspaceId) -> anyhow::Result<Workspace> {
        todo!()
    }
}

impl<T: ToString> From<T> for Code {
    fn from(value: T) -> Self {
        let cwd = value.to_string();

        // VS code stores the path without any trailing slashes.
        // We need to canonicalize the path to remove any trailing slashes.
        let cwd = PathBuf::from(&cwd)
            .canonicalize()
            .ok()
            .and_then(|p| p.to_str().map(|s| s.to_string()))
            .unwrap_or(cwd);

        // Find git root directory
        let git_root = std::process::Command::new("git")
            .arg("rev-parse")
            .arg("--show-toplevel")
            .current_dir(&cwd)
            .output()
            .ok()
            .and_then(|output| {
                if output.status.success() {
                    String::from_utf8(output.stdout)
                        .ok()
                        .map(|s| s.trim().to_string())
                } else {
                    None
                }
            })
            .unwrap_or(cwd.clone());

        Self { cwd: git_root, code_info: Platforms::default() }
    }
}
