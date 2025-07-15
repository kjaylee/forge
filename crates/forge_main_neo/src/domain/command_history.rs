use std::path::PathBuf;

use anyhow::Result;

use crate::history::{FileBackedHistory, HistoryItem};

/// Command history wrapper around our simplified FileBackedHistory with
/// navigation tracking
#[derive(Debug)]
pub struct CommandHistory {
    /// Our simplified file-backed history implementation
    history: FileBackedHistory,
    /// Current navigation position
    current_index: Option<usize>,
}

impl CommandHistory {
    /// Create a new CommandHistory with a specified max size and file path
    pub fn with_file(max_size: usize, path: PathBuf) -> Result<Self> {
        let history = FileBackedHistory::with_file(max_size, path)?;
        Ok(Self { history, current_index: None })
    }

    /// Add a command to history with LRU behavior and file persistence
    pub fn add_command(&mut self, command: String) -> Result<()> {
        self.history.save(HistoryItem::new(command))?;
        // Reset navigation state
        self.current_index = None;
        Ok(())
    }

    /// Navigate to previous command (up arrow)
    pub fn navigate_up(&mut self) -> Option<String> {
        if self.history.total_entries() == 0 {
            return None;
        }

        match self.current_index {
            None => {
                // Start navigation from most recent (index 0)
                self.current_index = Some(self.history.total_entries() - 1);
                self.get_command_at_index(self.history.total_entries() - 1)
            }
            Some(0) => {
                self.current_index = None;
                None // No previous command, reset navigation
            }
            Some(index) => {
                // Move to older command if possible
                self.current_index = Some(index - 1);
                self.get_command_at_index(index - 1)
            }
        }
    }

    /// Navigate to next command (down arrow)
    pub fn navigate_down(&mut self) -> Option<String> {
        match self.current_index {
            None => {
                self.current_index = Some(0);
                self.get_command_at_index(0)
            }
            Some(index) => {
                if index + 1 < self.history.total_entries() {
                    // Move to newer command if possible
                    self.current_index = Some(index + 1);
                    self.get_command_at_index(index + 1)
                } else {
                    // No newer command, reset navigation
                    self.current_index = None;
                    None
                }
            }
        }
    }

    /// Get command at a specific index from the most recent (0 = most recent)
    fn get_command_at_index(&self, index: usize) -> Option<String> {
        self.history.get(index).map(|item| item.item.clone())
    }

    /// Get autocomplete suggestion for current input
    pub fn get_autocomplete_suggestion(&self, current_input: &str) -> Option<String> {
        if current_input.trim().is_empty() {
            return None;
        }

        // Search for commands that start with current input
        let results = self.history.search_prefix(current_input);

        if results.is_empty() {
            None
        } else {
            // Return the most recent matching command
            Some(results[0].item.clone())
        }
    }

    /// Reset navigation state (called when user types)
    pub fn reset_navigation(&mut self) {
        self.current_index = None;
    }

    /// Get the number of commands in history
    pub fn len(&self) -> usize {
        self.history.total_entries()
    }

    /// Check if history is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Flush history to file
    pub fn flush(&mut self) -> Result<()> {
        self.history.sync().map_err(|e| anyhow::anyhow!(e))
    }
}
