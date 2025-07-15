use std::collections::VecDeque;
use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::sync::Arc;

use crate::history::HistoryItem;

/// Simple file-backed history implementation
#[derive(Debug, Clone)]
pub struct FileBackedHistory {
    /// In-memory storage with LRU behavior
    items: VecDeque<HistoryItem>,
    /// Maximum capacity
    capacity: usize,
    /// File for persistence
    file: Arc<File>,
}

impl FileBackedHistory {
    /// Create a new file-backed history with specified capacity and file path
    pub fn with_file(capacity: usize, file_path: PathBuf) -> anyhow::Result<Self> {
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .append(true)
            .open(&file_path)?;
        let mut history = Self {
            items: VecDeque::with_capacity(capacity),
            capacity,
            file: Arc::new(file),
        };
        // Load existing history from file if it exists
        history.sync_from_file()?;
        Ok(history)
    }

    /// Add a new command to history
    pub fn save(&mut self, item: HistoryItem) -> anyhow::Result<()> {
        // Don't add empty or whitespace-only commands
        let trimmed_command = item.item.trim().to_string();
        if trimmed_command.is_empty() {
            return Ok(());
        }

        let new_item = HistoryItem::new(trimmed_command);
        self.items.retain(|existing| existing.item != new_item.item);

        // Add to front (most recent)
        self.file
            .write(format!("{}\n", escape(&new_item.item)).as_bytes())?;
        self.items.push_front(new_item);

        // Maintain capacity
        while self.items.len() > self.capacity {
            self.items.pop_back();
        }

        Ok(())
    }

    /// Get command at index from most recent (0 = most recent)
    pub fn get(&self, index: usize) -> Option<&HistoryItem> {
        self.items.get(index)
    }

    /// Find commands that start with the given prefix
    pub fn search_prefix(&self, prefix: &str) -> Vec<&HistoryItem> {
        self.items
            .iter()
            .filter(|item| item.item.starts_with(prefix))
            .collect()
    }

    /// Sync to file (explicit flush)
    pub fn sync(&mut self) -> anyhow::Result<()> {
        self.sync_to_file()
    }

    pub fn total_entries(&self) -> usize {
        self.items.len()
    }

    /// Load history from file
    fn sync_from_file(&mut self) -> anyhow::Result<()> {
        let mut content = String::new();
        self.file.read_to_string(&mut content)?;

        let lines: Vec<&str> = content.lines().collect();
        let total_commands = lines.len();
        let skip_lines = total_commands.saturating_sub(self.capacity);
        for line in lines.into_iter().skip(skip_lines) {
            let line = line.trim();
            if !line.is_empty() {
                self.items.push_front(HistoryItem::new(unescape(line)));
            }
        }

        Ok(())
    }

    /// Save history to file
    fn sync_to_file(&mut self) -> anyhow::Result<()> {
        let content: String = self
            .items
            .iter()
            .map(|item| escape(item.item.as_str()))
            .collect::<Vec<_>>()
            .join("\n");

        self.file.write(format!("{content}\n").as_bytes())?;
        Ok(())
    }
}

fn escape(s: &str) -> String {
    s.replace('\n', "<\\n>")
}

fn unescape(s: &str) -> String {
    s.replace("<\\n>", "\n")
}
