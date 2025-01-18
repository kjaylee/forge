use std::path::PathBuf;

use forge_domain::{ActiveFiles, CodeInfo};
use rusqlite::{Connection, OptionalExtension};
use serde_json::Value;

use crate::platform::Platforms;

pub struct ForgeVsCode {
    cwd: String,
    code_info: Platforms,
}

impl ActiveFiles for ForgeVsCode {
    fn active_files(&self) -> anyhow::Result<Vec<String>> {
        self.active_files_inner(false, 0)
    }
}

impl ForgeVsCode {
    fn active_files_inner(&self, try_ceil: bool, i: i8) -> anyhow::Result<Vec<String>> {
        if !self.code_info.is_running() {
            return Ok(vec![]);
        }
        let hash = self.code_info.hash_path(&self.cwd, try_ceil)?;
        let vs_code_path = self
            .code_info
            .vs_code_path()
            .ok_or(anyhow::anyhow!("No VS Code path found"))?;
        let db_path = format!(
            "{}/User/workspaceStorage/{}/state.vscdb",
            vs_code_path, hash
        );

        let conn = Connection::open(db_path);
        if conn.is_err() && i == 0 {
            return self.active_files_inner(true, 1);
        }
        let conn = conn?;
        let key = "workbench.explorer.treeViewState";

        let mut stmt = conn.prepare("SELECT value FROM ItemTable WHERE key = ?1")?;
        let value: Option<String> = stmt
            .query_row(rusqlite::params![key], |row| row.get(0))
            .optional()?;
        if let Some(value) = value {
            return Self::extract_fspaths(&value).map(|v| {
                v.into_iter()
                    .map(|v| format!("<vs_code_active_file>{v}</vs_code_active_file>"))
                    .collect()
            });
        }
        Ok(vec![])
    }
}

impl<T: ToString> From<T> for ForgeVsCode {
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

impl ForgeVsCode {
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
