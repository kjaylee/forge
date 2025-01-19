use std::collections::HashSet;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use anyhow::anyhow;
use forge_walker::Walker;
use rusqlite::{Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sysinfo::System;

use async_trait::async_trait;
use forge_domain::{Ide, IdeRepository, Workspace, WorkspaceId};

/// Represents Visual Studio Code IDE interaction
pub struct Code {
    cwd: String,
}

impl Code {
    /// Create a new Code instance with a custom working directory
    pub fn new<T: ToString>(cwd: T) -> Self {
        let cwd = cwd.to_string();

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

        Self { cwd: git_root }
    }
}

#[async_trait]
impl IdeRepository for Code {
    async fn get_active_ides(&self) -> anyhow::Result<Vec<Ide>> {
        get_all_vscode_instances(&self.cwd).await
    }

    async fn get_workspace(&self, ide: &WorkspaceId) -> anyhow::Result<Workspace> {
        get_workspace_inner(ide.clone(), ide.as_str(), &self.cwd).await
    }
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Storage {
    windows_state: WindowState,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct WindowState {
    last_active_window: LastActiveWindow,
    opened_windows: Vec<LastActiveWindow>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct LastActiveWindow {
    folder: String,
}

async fn extract_workspace_id(args: &[String], cwd: &str, index: usize) -> anyhow::Result<String> {
    let code_dir = extract_storage_dir(args).ok_or(anyhow!("Failed to extract storage directory"))?;
    let storage_file = PathBuf::from(format!("{}/User/globalStorage/storage.json", code_dir));
    let storage_json = std::fs::read_to_string(storage_file)?;
    let json: Storage = serde_json::from_str(&storage_json)?;
    let path_buf = PathBuf::from(code_dir.clone())
        .join("User")
        .join("workspaceStorage");
    let cwd = convert_path(cwd);

    // Not sure if matching index is good idea.
    let search_dir = if json
        .windows_state
        .opened_windows
        .iter()
        .enumerate()
        .any(|(i, folder)| {
            i == index
                && folder
                .folder
                .strip_prefix("file://")
                .map(convert_path)
                .unwrap_or_default()
                .eq(&cwd)
        }) {
        cwd
    } else if json
        .windows_state
        .last_active_window
        .folder
        .strip_prefix("file://")
        .map(convert_path)
        .unwrap_or_default()
        .eq(&cwd)
    {
        cwd
    } else {
        return Err(anyhow!("Project not active in VS code"));
    };

    let hash_file = get_hash(Walker::new(path_buf.clone()), &search_dir, path_buf).await?;

    Ok(hash_file
        .path
        .split('/')
        .last()
        .unwrap_or_default()
        .to_string())
}

fn convert_path(v: &str) -> String {
    if std::env::consts::OS == "windows" {
        let v = urlencoding::decode(v)
            .map(|v| v.to_string())
            .unwrap_or(v.to_string());
        let v = v.split(":").last().unwrap_or(&v);
        typed_path::WindowsPath::new(v)
            .with_unix_encoding()
            .to_string()
    } else {
        v.to_string()
    }
}

fn extract_storage_dir(args: &[String]) -> Option<String> {
    args.iter()
        .find_map(|v| find_arg_value(&[v.clone()], "--user-data-dir="))
}

async fn get_all_vscode_instances(cwd: &str) -> anyhow::Result<Vec<Ide>> {
    let mut ans = vec![];
    let mut system = System::new_all();
    system.refresh_all();

    for (i, v) in system
        .processes()
        .values()
        .filter(|process| {
            process.name().to_ascii_lowercase() == "electron" // for linux
                || process.name().to_ascii_lowercase() == "code helper (renderer)"  // for macos
                || process.name().to_ascii_lowercase() == "code.exe" // for windows
        })
        .filter(|process| {
            process
                .cmd()
                .iter()
                .any(|arg| arg.to_string_lossy().contains("vscode-window-config"))
        })
        .enumerate()
    {
        let cmd = v
            .cmd()
            .iter()
            .map(|v| v.to_string_lossy().to_string())
            .collect::<Vec<_>>();
        if let Ok(workspace_id) = extract_workspace_id(&cmd, cwd, i).await {
            ans.push(Ide {
                name: "VS Code".to_string(),
                version: None,
                process: v.pid().as_u32().into(),
                working_directory: v
                    .cwd()
                    .unwrap_or(Path::new(""))
                    .to_string_lossy()
                    .to_string()
                    .into(),
                workspace_id: workspace_id.into(),
            });
        }
    }

    Ok(ans)
}

async fn get_hash(
    walker: Walker,
    cwd: &str,
    workspace_storage_path: PathBuf,
) -> anyhow::Result<forge_walker::File> {
    let dirs = walker
        .with_max_depth(1)
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
        .filter(|v| v.is_dir)
        .collect::<HashSet<_>>();

    dirs.into_iter()
        .find(|v| process_workflow_file(Path::new(&v.path), cwd))
        .ok_or(anyhow!("Project not found"))
}

async fn get_workspace_inner(workspace_id: WorkspaceId, vs_code_path: &str, cwd: &str) -> anyhow::Result<Workspace> {
    let mut ans = Workspace::default().workspace_id(workspace_id);

    let workspace_storage_path = Path::new(vs_code_path)
        .join("User")
        .join("workspaceStorage");
    let walker = Walker::new(workspace_storage_path.clone());

    if let Ok(project_hash) = get_hash(walker, cwd, workspace_storage_path).await {
        let conn = Connection::open(
            PathBuf::from(project_hash.path)
                .join("state.vscdb")
                .to_string_lossy()
                .to_string(),
        )?;

        ans = ans.focused_file(extract_focused_file(&conn)?);
        ans = ans.opened_files(extract_active_files(&conn)?);
    }
    Ok(ans)
}

fn extract_active_files(conn: &Connection) -> anyhow::Result<Vec<PathBuf>> {
    let key = "memento/workbench.parts.editor";
    let mut stmt = conn.prepare("SELECT value FROM ItemTable WHERE key = ?1")?;
    let value: Option<String> = stmt
        .query_row(rusqlite::params![key], |row| row.get(0))
        .optional()?;

    if let Some(value) = value {
        return Ok(active_files_path(&value)?);
    }

    Err(anyhow!("Focused file not found"))
}

fn active_files_path(json_data: &str) -> anyhow::Result<Vec<PathBuf>> {
    let parsed: Value = serde_json::from_str(json_data).expect("Invalid JSON");

    let mut fspaths = vec![];

    // Recursively search for "fsPath" keys
    fn find_fspaths(
        value: &Value,
        fspaths: &mut Vec<PathBuf>,
        possible_value: bool,
    ) -> anyhow::Result<()> {
        match value {
            Value::Object(map) => {
                for (key, val) in map {
                    if key == "fsPath" {
                        if let Value::String(path) = val {
                            fspaths.push(PathBuf::from(path));
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

fn extract_focused_file(connection:& Connection) -> anyhow::Result<PathBuf> {
    let key = "workbench.explorer.treeViewState";
    let mut stmt = connection.prepare("SELECT value FROM ItemTable WHERE key = ?1")?;
    let value: Option<String> = stmt
        .query_row(rusqlite::params![key], |row| row.get(0))
        .optional()?;

    if let Some(value) = value {
        return Ok(PathBuf::from(focused_file_path(&value)?));
    }
    
    Err(anyhow!("Focused file not found"))
}


fn process_workflow_file(path: &Path, cwd: &str) -> bool {
    let path = path.join("workspace.json");

    if let Ok(content) = std::fs::read_to_string(&path) {
        let workflow_json: Value = serde_json::from_str(&content).unwrap_or_default();

        if let Some(folder) = workflow_json.get("folder").and_then(|v| v.as_str()) {
            // Remove "file://" prefix
            let project_path = convert_path(folder.strip_prefix("file://").unwrap_or(folder));

            // Check if the project path matches or is a parent of the current working
            // directory
            if cwd.starts_with(&project_path) {
                return true;
            }
        }
    }

    false
}

fn focused_file_path(json_data: &str) -> anyhow::Result<String> {
    // Parse the input JSON into a `serde_json::Value`
    let data: Value = serde_json::from_str(json_data)?;

    // Extract the "focus" array, if it exists
    let focus_array = match data.get("focus") {
        Some(Value::Array(arr)) => arr,
        _ => return Err(anyhow!("Invalid focus json")), // "focus" key not found or not an array
    };

    // Get the first item from "focus", ensuring it's a string
    if let Some(Value::String(item)) = focus_array.first() {
        // The string looks like "file://...::file://..."
        // If you want the second half (the actual file path), split by "::"
        return if let Some(idx) = item.find("::") {
            let second_part = &item[idx + 2..]; // after the "::"
            Ok(second_part
                .strip_prefix("file://")
                .unwrap_or(second_part)
                .to_string())
        } else {
            // If there's no "::", just return the entire string
            Ok(item.clone())
        };
    }

    // No first item in the array or it's not a string
    Err(anyhow!("Invalid 'focus' array"))
}

fn find_arg_value(cmd: &[String], key: &str) -> Option<String> {
    for arg in cmd {
        if let Some(pos) = arg.find(key) {
            // Extract the substring starting after the key
            let value_with_rest = &arg[pos + key.len()..];

            // Check if the extracted value starts and ends cleanly (handle multi-word
            // paths)
            if value_with_rest.contains(" --") {
                // Extract up to the first occurrence of " --"
                if let Some(end_pos) = value_with_rest.find(" --") {
                    return Some(value_with_rest[..end_pos].to_string());
                }
            } else {
                // If no " --" exists, return the whole value
                return Some(value_with_rest.to_string());
            }
        }
    }
    None
}
