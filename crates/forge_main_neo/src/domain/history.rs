use std::path::PathBuf;

use anyhow::Result;

use crate::history::{FileBackedHistory, HistoryItem};

/// History search state for recursive search functionality
#[derive(Debug, Default, Clone)]
pub struct HistorySearchState {
    /// Whether search mode is active
    pub is_active: bool,
    /// Current search query
    pub query: String,
    /// Current match index in search results
    pub current_match_index: usize,
    /// Cached search results
    pub matches: Vec<String>,
}

impl HistorySearchState {
    /// Enter search mode with an optional initial query
    pub fn enter_search(&mut self, initial_query: Option<String>) {
        self.is_active = true;
        self.query = initial_query.unwrap_or_default();
        self.current_match_index = 0;
        self.matches.clear();
    }

    /// Exit search mode and reset state
    pub fn exit_search(&mut self) {
        self.is_active = false;
        self.query.clear();
        self.current_match_index = 0;
        self.matches.clear();
    }

    /// Update search query and reset match index
    pub fn update_query(&mut self, query: String) {
        self.query = query;
        self.current_match_index = 0;
        self.matches.clear();
    }

    /// Navigate to next match
    pub fn next_match(&mut self) {
        if !self.matches.is_empty() && self.current_match_index < self.matches.len() - 1 {
            self.current_match_index += 1;
        }
    }

    /// Navigate to previous match
    pub fn prev_match(&mut self) {
        if self.current_match_index > 0 {
            self.current_match_index -= 1;
        }
    }

    /// Get current match if available
    pub fn current_match(&self) -> Option<String> {
        self.matches.get(self.current_match_index).cloned()
    }

    /// Update search results based on current query
    pub fn update_search(&mut self, history: &History) {
        self.matches = history.search(&self.query);
        self.current_match_index = 0;
    }

    /// Get search status string for display
    pub fn status_text(&self) -> String {
        if self.matches.is_empty() {
            if self.query.is_empty() {
                "reverse-i-search: ".to_string()
            } else {
                format!("failing reverse-i-search: {}", self.query)
            }
        } else {
            format!(
                "reverse-i-search: {} [{}/{}]",
                self.query,
                self.current_match_index + 1,
                self.matches.len()
            )
        }
    }
}
/// Command history wrapper around our simplified FileBackedHistory with
/// navigation tracking
#[derive(Debug)]
pub struct History {
    /// Our simplified file-backed history implementation
    history: FileBackedHistory,
    /// Current navigation position
    current_index: Option<usize>,
}

impl History {
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

    /// Search history with a query and update search state
    pub fn search(&self, query: &str) -> Vec<String> {
        if query.trim().is_empty() {
            return Vec::new();
        }

        // Search for commands that contain the query (not just prefix)
        self.history
            .get_all_items()
            .iter()
            .filter(|item| item.item.contains(query))
            .map(|item| item.item.clone())
            .collect()
    }

    /// Alias for search method to match key handler expectations
    pub fn search_history(&self, query: &str) -> Vec<String> {
        self.search(query)
    }

    /// Get all commands for search (most recent first)
    pub fn get_all_commands(&self) -> Vec<String> {
        self.history
            .get_all_items()
            .iter()
            .map(|item| item.item.clone())
            .collect()
    }
}
