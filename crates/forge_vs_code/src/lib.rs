#[cfg(target_os = "linux")]
mod linux;
mod vs_code;

pub use vs_code::*;

pub trait CodeInfo {
    fn hash_path(&self, folder_path: &str) -> anyhow::Result<String>;
    fn vs_code_path(&self) -> Option<String>;
    
    /// Check if VS Code is currently running
    ///
    /// This function checks for running VS Code processes.
    /// It considers multiple potential executable names.
    ///
    /// # Returns
    /// A boolean indicating whether VS Code is running.
    fn is_running(&self) -> bool;
}
