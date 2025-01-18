use std::collections::HashSet;

use forge_domain::Ide;
use sysinfo::System;

#[derive(Default)]
pub struct UnixCodeInfo;

impl Ide for UnixCodeInfo {
    fn installation_path(&self) -> Option<Vec<String>> {
        get_user_data_dir()
    }

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

fn get_user_data_dir() -> Option<Vec<String>> {
    // Initialize the system and refresh process information
    let mut system = System::new_all();
    system.refresh_all();
    let mut ans: Option<HashSet<String>> = None;

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
                let mut tmp: HashSet<String> = ans.unwrap_or_default();
                tmp.insert(value);
                ans = Some(tmp);
            }
        }
    }

    ans.map(|v| v.into_iter().collect())
}
