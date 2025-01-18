use sysinfo::System;

use crate::CodeInfo;

#[derive(Default)]
pub struct LinuxCodeInfo;

impl CodeInfo for LinuxCodeInfo {
    fn hash_path(&self, folder_path: &str) -> anyhow::Result<String> {
        hash_path(folder_path)
    }

    fn vs_code_path(&self) -> Option<String> {
        get_user_data_dir()
    }
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

fn get_user_data_dir() -> Option<String> {
    // Initialize the system and refresh process information
    let mut system = System::new_all();
    system.refresh_all();

    // Iterate over all processes
    for process in system.processes().values() {
        let cmd = process.cmd();
        let cmd = cmd
            .iter()
            .map(|v| v.to_string_lossy().to_string())
            .collect::<Vec<_>>();

        // Check if the process contains "code" and "vscode-window-config"
        if cmd.iter().any(|arg| arg.contains("code"))
            && cmd.iter().any(|arg| arg.contains("vscode-window-config"))
        {
            // Look for the "--user-data-dir" argument dynamically
            if let Some(value) = find_arg_value(&cmd, "--user-data-dir=") {
                return Some(value);
            }
        }
    }

    None
}

fn hash_path(folder_path: &str) -> anyhow::Result<String> {
    use std::os::unix::fs::MetadataExt;

    let metadata = std::fs::metadata(folder_path)?;

    // Get the inode (st_ino) as the salt
    let inode = metadata.ino();

    // Create the hash using the folder path and inode
    let mut hasher = md5::Context::new();
    hasher.consume(folder_path.as_bytes());
    hasher.consume(inode.to_string().as_bytes());

    Ok(format!("{:x}", hasher.compute()))
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_linux() {
        let path = "/tmp";
        let hash = hash_path(path).unwrap();
        assert_eq!(hash, "aeebaf534f75fece5857a978463aba33");
    }
    #[test]
    fn test_get_user_data_dir() {
        let user_data_dir = get_user_data_dir();
        println!("User data dir: {:?}", user_data_dir);
    }
}
