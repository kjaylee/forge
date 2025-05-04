/// Output from a command execution
pub struct CommandOutput {
    pub command: String,
    pub stdout: String,
    pub stderr: String,
    pub exit_code: Option<i32>,
}

impl CommandOutput {
    pub fn success(&self) -> bool {
        self.exit_code.map_or(true, |code| code >= 0)
    }
}
