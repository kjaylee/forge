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
        let key = "memento/workbench.parts.editor";

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
    fn extract_fspaths(json_data: &str) -> anyhow::Result<Vec<String>> {
        let parsed: Value = serde_json::from_str(json_data).expect("Invalid JSON");

        let mut fspaths = vec![];

        // Recursively search for "fsPath" keys
        fn find_fspaths(
            value: &Value,
            fspaths: &mut Vec<String>,
            possible_value: bool,
        ) -> anyhow::Result<()> {
            match value {
                Value::Object(map) => {
                    for (key, val) in map {
                        if key == "fsPath" {
                            if let Value::String(path) = val {
                                fspaths.push(path.clone());
                            }
                        } else {
                            find_fspaths(val, fspaths, key == "value" || possible_value)?;
                        }
                    }
                    Ok(())
                }
                Value::Array(arr) => {
                    for item in arr {
                        find_fspaths(item, fspaths, false)?;
                    }
                    Ok(())
                }
                Value::String(v) if possible_value => {
                    let new_value: Value = serde_json::from_str(v)?;
                    find_fspaths(&new_value, fspaths, false)
                }
                _ => Ok(()),
            }
        }

        find_fspaths(&parsed, &mut fspaths, false)?;

        Ok(fspaths)
    }
}
