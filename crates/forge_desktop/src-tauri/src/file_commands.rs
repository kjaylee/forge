use std::path::{Path, PathBuf};
use std::{env, fs};

use serde::{Deserialize, Serialize};
use tauri::{command, AppHandle};
use tokio::runtime::Runtime;

use crate::commands::get_current_project;

#[derive(Serialize, Deserialize)]
pub struct FileInfo {
    name: String,
    extension: String,
    size: u64,
    is_file: bool,
    is_directory: bool,
    is_symlink: bool,
    created_at: Option<u64>,
    modified_at: Option<u64>,
}

/// Helper to normalize a path that might have duplication issues
fn normalize_path(path: &str, app_handle: Option<&AppHandle>) -> String {
    // Get the current project path from state if available
    let base_path = if let Some(handle) = app_handle {
        // Use the get_current_project command to get the project info
        let rt = Runtime::new().ok();
        if let Some(runtime) = rt {
            if let Some(project_info) =
                runtime.block_on(async { get_current_project(handle.clone()).await })
            {
                project_info.path
            } else {
                // No project selected, just return the original path
                return path.to_string();
            }
        } else {
            // Failed to create runtime, return the original path
            return path.to_string();
        }
    } else {
        // No app_handle available, just return the original path
        return path.to_string();
    };

    // Check if path contains duplication of the base path
    let path_str = path.to_string();

    // First check for exact duplication like "base_path/base_path/..."
    let dup_path = format!("{}/{}", base_path, base_path.trim_start_matches('/'));
    let clean_path = path_str.replace(&dup_path, &base_path);

    // Check for more complex duplication patterns
    if let Some(rel_path) = clean_path.strip_prefix(&base_path) {
        if rel_path.starts_with(&base_path) || rel_path.starts_with(&format!("/{}", base_path)) {
            // We have a duplication pattern
            // Extract everything after the second base_path occurrence
            if let Some(unique_part) = rel_path.strip_prefix(&base_path) {
                return format!("{}{}", base_path, unique_part);
            } else if let Some(unique_part) = rel_path.strip_prefix(&format!("/{}", base_path)) {
                return format!("{}{}", base_path, unique_part);
            }
        }
    }

    clean_path
}

/// Helper to resolve a file path that might be relative to the app or current
/// directory
fn resolve_path(path: &str, app_handle: Option<&AppHandle>) -> PathBuf {
    // First normalize the path to handle any duplication
    let normalized_path = normalize_path(path, app_handle);
    let path_obj = Path::new(&normalized_path);

    // If the path is absolute, use it directly
    if path_obj.is_absolute() {
        return path_obj.to_path_buf();
    }

    // Try different base paths to find the file

    // 1. Try with current working directory
    if let Ok(cwd) = env::current_dir() {
        let potential_path = cwd.join(&normalized_path);
        if potential_path.exists() {
            return potential_path;
        }
    }

    // 2. Try with executable directory
    if let Ok(exe_path) = env::current_exe() {
        if let Some(exe_dir) = exe_path.parent() {
            let potential_path = exe_dir.join(&normalized_path);
            if potential_path.exists() {
                return potential_path;
            }

            // Try going up a few levels (for development environments)
            for i in 1..5 {
                let mut ancestor = exe_dir.to_path_buf();
                for _ in 0..i {
                    if let Some(parent) = ancestor.parent() {
                        ancestor = parent.to_path_buf();
                    } else {
                        break;
                    }
                }

                let potential_path = ancestor.join(&normalized_path);
                if potential_path.exists() {
                    return potential_path;
                }
            }
        }
    }

    // Fall back to the original path if no resolution works
    path_obj.to_path_buf()
}

/// Read the content of a file as text
#[command]
pub fn read_file_content(path: &str, app_handle: AppHandle) -> Result<String, String> {
    let resolved_path = resolve_path(path, Some(&app_handle));
    fs::read_to_string(&resolved_path).map_err(|e| {
        format!(
            "Failed to read file: {} (resolved path: {:?})",
            e, resolved_path
        )
    })
}

/// Read file metadata
#[command]
pub fn get_file_info(path: &str, app_handle: AppHandle) -> Result<FileInfo, String> {
    let resolved_path = resolve_path(path, Some(&app_handle));
    let path_obj = &resolved_path;
    let metadata = fs::metadata(&resolved_path).map_err(|e| {
        format!(
            "Failed to read file metadata: {} (resolved path: {:?})",
            e, resolved_path
        )
    })?;

    let file_name = path_obj.file_name().and_then(|n| n.to_str()).unwrap_or("");

    let extension = path_obj.extension().and_then(|e| e.to_str()).unwrap_or("");

    // Convert timestamps to milliseconds since UNIX epoch
    // These might be None on some platforms
    let created_at = metadata
        .created()
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|d| d.as_secs() * 1000 + d.subsec_millis() as u64);

    let modified_at = metadata
        .modified()
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|d| d.as_secs() * 1000 + d.subsec_millis() as u64);

    Ok(FileInfo {
        name: file_name.to_string(),
        extension: extension.to_string(),
        size: metadata.len(),
        is_file: metadata.is_file(),
        is_directory: metadata.is_dir(),
        is_symlink: metadata.is_symlink(),
        created_at,
        modified_at,
    })
}

/// Check if a file exists
#[command]
pub fn file_exists(path: &str, app_handle: AppHandle) -> bool {
    let resolved_path = resolve_path(path, Some(&app_handle));
    resolved_path.exists()
}
