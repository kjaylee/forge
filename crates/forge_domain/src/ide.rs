pub trait ActiveFiles {
    fn active_files(&self) -> anyhow::Result<Vec<String>>;
}
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
