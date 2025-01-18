pub trait ActiveFiles {
    fn active_files(&self) -> anyhow::Result<Vec<String>>;
}

/// Represents functionality for interacting with IDEs
///
/// This trait provides methods for retrieving VS Code-related information
/// and performing operations specific to the IDE environment.
///
/// # Methods
/// - `hash_path`: Generate a unique hash for a given folder path
/// - `vs_code_path`: Retrieve the installation path of VS Code
/// - `is_running`: Check if VS Code is currently running
///
/// # Purpose
/// The `CodeInfo` trait abstracts IDE-specific operations, enabling
/// cross-platform and flexible interactions with IDEs.
pub trait CodeInfo {
    /// Generates a unique hash for a given folder path
    ///
    /// This method creates a consistent, reproducible hash representing
    /// a specific folder path. Useful for tracking or identifying workspace
    /// locations.
    ///
    /// # Arguments
    /// * `folder_path` - A string slice representing the path to be hashed
    ///
    /// # Returns
    /// A `Result` containing the generated hash string, or an error if hashing
    /// fails
    ///
    /// # Examples
    fn hash_path(&self, folder_path: &str) -> anyhow::Result<String>;

    /// Retrieves the installation path of Visual Studio Code
    ///
    /// # Returns
    /// An `Option` containing the full path to the VS Code executable,
    /// or `None` if the path cannot be determined
    ///
    /// # Platform Considerations
    /// - The returned path may vary depending on the operating system
    /// - Returns `None` if VS Code is not installed or path is not discoverable
    fn vs_code_path(&self) -> Option<String>;

    /// Check if IDE is currently running
    ///
    /// This method determines whether VS Code is active in the system's
    /// process list. It supports multiple potential executable names
    /// to ensure cross-platform compatibility.
    ///
    /// # Returns
    /// `true` if VS Code is running, `false` otherwise
    ///
    /// # Platform Support
    /// - Works across different operating systems
    /// - Checks for variations of VS Code executable names
    ///
    /// # Performance
    /// Lightweight method that performs a quick process check
    fn is_running(&self) -> bool;
}
