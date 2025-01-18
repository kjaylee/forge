use std::time::UNIX_EPOCH;

use forge_domain::CodeInfo;
use sysinfo::System;

#[derive(Default)]
pub struct MacOsCodeInfo;

impl CodeInfo for MacOsCodeInfo {
    fn hash_path(&self, folder_path: &str, try_ceil: bool) -> anyhow::Result<String> {
        hash_path(folder_path, try_ceil)
    }

    fn vs_code_path(&self) -> Option<String> {
        get_user_data_dir()
    }

    /// Check if VS Code is currently running
    ///
    /// This function uses the `ps aux | grep` command to check for running VS
    /// Code renderer processes.
    ///
    /// # Returns
    /// A boolean indicating whether VS Code is running.
    fn is_running(&self) -> bool {
        match std::process::Command::new("sh")
            .arg("-c")
            .arg("ps aux | grep -i \"[c]ode.*renderer\"")
            .output()
        {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                !stdout.is_empty() && output.status.success()
            }
            Err(e) => {
                eprintln!("Error checking VSCode status: {}", e);
                false
            }
        }
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

fn micros_to_millis_ceil(micros: u128) -> u128 {
    (micros + 999) / 1000
}

fn hash_path(folder_path: &str, try_ceil: bool) -> anyhow::Result<String> {
    let metadata = std::fs::metadata(folder_path)?;

    // Create the hash using the folder path and inode
    let mut hasher = md5::Context::new();

    // Get the birthtime (creation time) as the salt
    let mut inode = metadata.created()?.duration_since(UNIX_EPOCH)?.as_micros();
    if try_ceil {
        inode = micros_to_millis_ceil(inode);
    }

    hasher.consume(folder_path);
    hasher.consume(inode.to_string());

    Ok(format!("{:x}", hasher.compute()))
}
