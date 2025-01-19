use std::collections::HashSet;
use std::path::{Path, PathBuf};
use anyhow::anyhow;
use rusqlite::{Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use forge_domain::Ide;
use forge_walker::Walker;


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
    let path_buf = PathBuf::from(code_dir.clone()).join("User/workspaceStorage");

    // Not sure if matching index is good idea.
    let search_dir = if json.windows_state.last_active_window.folder.strip_prefix("file://").unwrap_or_default().eq(cwd) && index == 0 {
        cwd
    } else if json.windows_state.opened_windows.iter().enumerate().any(|(i,folder)| i == index && folder.folder.strip_prefix("file://").unwrap_or_default().eq(cwd)) {
        cwd
    } else {
        return Err(anyhow!("Project not active in VS code"));
    };

    let hash_file = get_hash(Walker::new(path_buf.clone()), search_dir, path_buf).await?;

    Ok(hash_file.path.split('/').last().unwrap_or_default().to_string())
}

fn extract_storage_dir(args: &[String]) -> Option<String> {
    args.iter().find(|v| v.contains("vscode-window-config")).and_then(|v| find_arg_value(&[v.clone()], "--user-data-dir="))
}

async fn get_all_ides(cwd: &str) -> anyhow::Result<Vec<Ide>> {
    let mut ans = vec![];

    for (i, v) in procfs::process::all_processes()?
        .filter_map(|v| v.ok())
        .filter(|v| v.status().is_ok())
        .filter(|v| v.status().as_ref().unwrap().name == "electron")
        .filter(|v| v.cmdline().is_ok())
        .filter(|v| v.cwd().is_ok())
        .filter(|v| v.cmdline().unwrap().iter().any(|v| v.contains("vscode-window-config")))
        .enumerate() {

        if let Ok(workspace_id) = extract_workspace_id(&v.cmdline().unwrap_or_default(), cwd, i).await {
            ans.push(Ide {
                name: "VS Code".to_string(),
                version: None,
                process: (v.pid() as u32).into(),
                working_directory: v.cwd().unwrap_or_default().into(),
                workspace_id: workspace_id.into(),
            });
        }
    }

    Ok(ans)
}

async fn get_hash(walker: Walker, cwd: &str, workspace_storage_path: PathBuf) -> anyhow::Result<forge_walker::File> {
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

    dirs
        .into_iter()
        .find(|v| process_workflow_file(Path::new(&v.path), cwd)).ok_or(anyhow!("foo"))
}

async fn active_files_inner(vs_code_path: &str, cwd: &str) -> anyhow::Result<Vec<String>> {
    let workspace_storage_path = Path::new(&vs_code_path).join("User/workspaceStorage");
    let walker = Walker::new(workspace_storage_path.clone());


    if let Ok(project_hash) = get_hash(walker, cwd, workspace_storage_path).await {
        let conn = Connection::open(format!("{}/state.vscdb", project_hash.path))?;
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
        println!("{:#?}", get_all_ides("/home/ssdd/RustroverProjects/code-forge").await.unwrap());
    }
}

