use std::ascii::AsciiExt;
use std::collections::HashSet;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use anyhow::anyhow;
use forge_domain::Ide;
use forge_walker::Walker;
use rusqlite::{Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sysinfo::System;

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
    let code_dir = extract_storage_dir(args).ok_or(anyhow!("foo"))?;
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

async fn get_all_ides(cwd: &str) -> anyhow::Result<Vec<Ide>> {
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
        .ok_or(anyhow!("xfoo"))
}

async fn active_files_inner(vs_code_path: &str, cwd: &str) -> anyhow::Result<Vec<String>> {
    let workspace_storage_path = Path::new(&vs_code_path)
        .join("User")
        .join("workspaceStorage");
    let walker = Walker::new(workspace_storage_path.clone());

    if let Ok(project_hash) = get_hash(walker, cwd, workspace_storage_path).await {
        let conn = Connection::open(
            PathBuf::from(project_hash.path)
                .join("state.vscdb")
                .to_string_lossy()
                .to_string(),
        );
        let conn = conn?;
        let key = "workbench.explorer.treeViewState";
        let mut stmt = conn.prepare("SELECT value FROM ItemTable WHERE key = ?1")?;
        let value: Option<String> = stmt
            .query_row(rusqlite::params![key], |row| row.get(0))
            .optional()?;

        if let Some(value) = value {
            return extract_fspaths(&value).map(|v| {
                v.into_iter()
                    .fold(HashSet::new(), |mut acc, v| {
                        acc.insert(v);
                        acc
                    })
                    .into_iter()
                    .collect()
            });
        }
    }

    Ok(vec![])
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

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_find_arg_value() {
        let x = "C:\\Users\\sr480\\RustroverProjects\\code-forge";
        // let x = convert_to_file_url(x).unwrap();
        println!("{:#?}", get_all_ides(&x).await.unwrap());
    }
}
