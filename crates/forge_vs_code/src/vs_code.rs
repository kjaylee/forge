use std::path::PathBuf;

use rusqlite::{Connection, OptionalExtension};
use serde_json::Value;

use crate::CodeInfo;

pub struct ForgeVsCode {
    cwd: String,
    code_info: Box<dyn CodeInfo>,
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

        #[cfg(target_os = "linux")]
        let code_info = crate::linux::LinuxCodeInfo;

        Self { cwd, code_info: Box::new(code_info) }
    }
}

impl ForgeVsCode {
    pub async fn active_files(&self) -> anyhow::Result<Vec<String>> {
        let hash = self.code_info.hash_path(&self.cwd)?;
        let vs_code_path = self
            .code_info
            .vs_code_path()
            .ok_or(anyhow::anyhow!("No VS Code path found"))?;
        let db_path = format!(
            "{}/User/workspaceStorage/{}/state.vscdb",
            vs_code_path, hash
        );

        let conn = Connection::open(db_path)?;
        let key = "memento/workbench.parts.editor";

        let mut stmt = conn.prepare("SELECT value FROM ItemTable WHERE key = ?1")?;
        let value: Option<String> = stmt
            .query_row(rusqlite::params![key], |row| row.get(0))
            .optional()?;
        if let Some(value) = value {
            return Self::extract_fspaths(&value);
        }
        Ok(vec![])
    }
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
