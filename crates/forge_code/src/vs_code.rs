use std::collections::HashSet;
use std::path::{Path, PathBuf};

use forge_domain::{ActiveFiles, Ide};
use forge_walker::Walker;
use rusqlite::{Connection, OptionalExtension};
use serde_json::Value;

use crate::platform::Platforms;

pub struct Code {
    cwd: String,
    code_info: Platforms,
}

#[async_trait::async_trait]
impl ActiveFiles for Code {
    async fn active_files(&self) -> anyhow::Result<Vec<String>> {
        self.active_files_inner().await
    }
}

impl Code {
    async fn active_files_inner(&self) -> anyhow::Result<Vec<String>> {
        let mut ans = vec![];
        if !self.code_info.is_running() {
            return Ok(ans);
        }

        let vs_code_paths = self
            .code_info
            .installation_path()
            .ok_or(anyhow::anyhow!("No VS Code path found"))?;

        for vs_code_path in vs_code_paths {
            let workspace_storage_path = Path::new(&vs_code_path).join("User/workspaceStorage");
            let walker = Walker::new(workspace_storage_path.clone());
            let dirs = walker
                .get()
                .await?
                .into_iter()
                .map(|mut v| {
                    v.path = workspace_storage_path
                        .join(v.path)
                        .to_string_lossy()
                        .to_string();
                    v
                })
                .collect::<HashSet<_>>();

            if let Some(project_hash) = dirs
                .into_iter()
                .find(|v| Self::process_workflow_file(Path::new(&v.path), &self.cwd))
            {
                let conn = Connection::open(format!("{}/state.vscdb", project_hash.path))?;
                let key = "workbench.explorer.treeViewState";
                let mut stmt = conn.prepare("SELECT value FROM ItemTable WHERE key = ?1")?;
                let value: Option<String> = stmt
                    .query_row(rusqlite::params![key], |row| row.get(0))
                    .optional()?;

                if let Some(value) = value {
                    ans.extend(Self::extract_fspaths(&value).map(|v| {
                        v.into_iter()
                            .fold(HashSet::new(), |mut acc, v| {
                                acc.insert(v);
                                acc
                            })
                            .into_iter()
                            .collect()
                    }));
                }
            }
        }

        Ok(ans)
    }

    fn process_workflow_file(path: &Path, cwd: &str) -> bool {
        let path = path.join("workspace.json");
        let cwd = Path::new(cwd);

        if let Ok(content) = std::fs::read_to_string(&path) {
            let workflow_json: Value = serde_json::from_str(&content).unwrap_or_default();

            if let Some(folder) = workflow_json.get("folder").and_then(|v| v.as_str()) {
                // Remove "file://" prefix
                let project_path = folder.strip_prefix("file://").unwrap_or(folder);

                // Check if the project path matches or is a parent of the current working
                // directory
                if cwd.starts_with(project_path) {
                    return true;
                }
            }
        }

        false
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

impl Code {
    fn extract_fspaths(json_data: &str) -> anyhow::Result<Option<String>> {
        // Parse the input JSON into a `serde_json::Value`
        let data: Value = serde_json::from_str(json_data)?;

        // Extract the "focus" array, if it exists
        let focus_array = match data.get("focus") {
            Some(Value::Array(arr)) => arr,
            _ => return Ok(None), // "focus" key not found or not an array
        };

        // Get the first item from "focus", ensuring it's a string
        if let Some(Value::String(item)) = focus_array.first() {
            // The string looks like "file://...::file://..."
            // If you want the second half (the actual file path), split by "::"
            return if let Some(idx) = item.find("::") {
                let second_part = &item[idx + 2..]; // after the "::"
                Ok(Some(
                    second_part
                        .strip_prefix("file://")
                        .unwrap_or(second_part)
                        .to_string(),
                ))
            } else {
                // If there's no "::", just return the entire string
                Ok(Some(item.clone()))
            };
        }

        // No first item in the array or it's not a string
        Ok(None)
    }
}
