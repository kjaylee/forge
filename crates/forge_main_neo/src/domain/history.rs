use std::collections::VecDeque;

use derive_setters::Setters;

/// History management with size limits and autocomplete functionality
#[derive(Clone, Debug, Setters)]
#[setters(strip_option, into)]
pub struct History {
    /// The entries in the history, most recent first
    entries: VecDeque<String>,
    /// Maximum number of entries to keep
    max_size: usize,
    /// Current position in history navigation (0 = most recent)
    current_position: Option<usize>,
}

impl Default for History {
    fn default() -> Self {
        Self::new(100) // Default to 100 entries
    }
}

impl History {
    /// Create a new history with the specified maximum size
    pub fn new(max_size: usize) -> Self {
        Self { entries: VecDeque::new(), max_size, current_position: None }
    }

    #[allow(dead_code)]
    pub fn is_active(&self) -> bool {
        self.current_position.is_some()
    }

    /// Add a new entry to the history
    /// If the entry already exists, it will be moved to the front
    /// If the history is at capacity, the oldest entry will be removed
    pub fn add_entry(&mut self, entry: String) {
        // Don't add empty entries
        if entry.trim().is_empty() {
            return;
        }

        // Remove the entry if it already exists to avoid duplicates
        self.entries.retain(|e| e != &entry);

        // Add to the front (most recent)
        self.entries.push_front(entry);

        // Enforce size limit by removing oldest entries
        while self.entries.len() > self.max_size {
            self.entries.pop_back();
        }

        // Reset navigation position
        self.current_position = None;
    }

    /// Returns entry matching the prefix, case-insensitive
    pub fn get_matching_entry(&self, prefix: &str) -> Option<(usize, String)> {
        if prefix.is_empty() {
            return self.entries.front().map(|entry| (0, entry.clone()));
        }

        let prefix_lower = prefix.to_lowercase();
        self.entries
            .iter()
            .enumerate()
            .find(|(_, entry)| entry.to_lowercase().starts_with(&prefix_lower))
            .map(|(idx, entry)| (idx, entry.clone()))
    }

    /// Navigate to the previous entry in history (older)
    pub fn navigate_previous(&mut self) -> Option<String> {
        if self.entries.is_empty() {
            return None;
        }

        let new_position = match self.current_position {
            None => 0,
            Some(pos) => {
                if pos + 1 < self.entries.len() {
                    pos + 1
                } else {
                    pos // Stay at the oldest entry
                }
            }
        };

        self.current_position = Some(new_position);
        self.entries.get(new_position).cloned()
    }

    /// Navigate to the next entry in history (newer)
    pub fn navigate_next(&mut self) -> Option<String> {
        match self.current_position {
            None => None,
            Some(0) => {
                // At the newest entry, reset to no selection and return empty string
                self.current_position = None;
                Some("".to_string())
            }
            Some(pos) => {
                let new_position = pos - 1;
                self.current_position = Some(new_position);
                self.entries.get(new_position).cloned()
            }
        }
    }

    /// Reset navigation position
    pub fn reset_navigation(&mut self) {
        self.current_position = None;
    }

    /// Get the current entry if navigating
    #[allow(dead_code)]
    pub fn current_entry(&self) -> Option<String> {
        self.current_position
            .and_then(|pos| self.entries.get(pos).cloned())
    }

    /// Get all entries (most recent first)
    #[allow(dead_code)]
    pub fn get_entries(&self) -> Vec<String> {
        self.entries.iter().cloned().collect()
    }

    /// Get the number of entries in history
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if history is empty
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[allow(dead_code)]
    pub fn set_current_position(&mut self, position: Option<usize>) {
        self.current_position = position;
    }

    /// Clear all history
    #[allow(dead_code)]
    pub fn clear(&mut self) {
        self.entries.clear();
        self.current_position = None;
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    fn create_test_history() -> History {
        let mut fixture = History::new(3);
        fixture.add_entry("first entry".to_string());
        fixture.add_entry("second entry".to_string());
        fixture.add_entry("third entry".to_string());
        fixture
    }

    #[test]
    fn test_new_history_is_empty() {
        let fixture = History::new(10);
        let actual = fixture.is_empty();
        let expected = true;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_add_entry_adds_to_front() {
        let mut fixture = History::new(10);
        fixture.add_entry("test entry".to_string());

        let actual = fixture.get_entries();
        let expected = vec!["test entry".to_string()];
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_add_entry_maintains_order() {
        let mut fixture = History::new(10);
        fixture.add_entry("first".to_string());
        fixture.add_entry("second".to_string());
        fixture.add_entry("third".to_string());

        let actual = fixture.get_entries();
        let expected = vec![
            "third".to_string(),
            "second".to_string(),
            "first".to_string(),
        ];
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_add_entry_removes_duplicates() {
        let mut fixture = History::new(10);
        fixture.add_entry("first".to_string());
        fixture.add_entry("second".to_string());
        fixture.add_entry("first".to_string()); // Duplicate

        let actual = fixture.get_entries();
        let expected = vec!["first".to_string(), "second".to_string()];
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_add_entry_enforces_size_limit() {
        let mut fixture = History::new(2);
        fixture.add_entry("first".to_string());
        fixture.add_entry("second".to_string());
        fixture.add_entry("third".to_string()); // Should remove "first"

        let actual = fixture.get_entries();
        let expected = vec!["third".to_string(), "second".to_string()];
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_add_entry_ignores_empty_strings() {
        let mut fixture = History::new(10);
        fixture.add_entry("".to_string());
        fixture.add_entry("   ".to_string());
        fixture.add_entry("valid".to_string());

        let actual = fixture.get_entries();
        let expected = vec!["valid".to_string()];
        assert_eq!(actual, expected);
    }

    // #[test]
    // fn test_get_matching_entries_with_empty_prefix() {
    //     let fixture = create_test_history();

    //     let actual = fixture.get_matching_entry("");
    //     let expected = vec![
    //         "third entry".to_string(),
    //         "second entry".to_string(),
    //         "first entry".to_string(),
    //     ];
    //     assert_eq!(actual, expected);
    // }

    // #[test]
    // fn test_get_matching_entries_with_prefix() {
    //     let fixture = create_test_history();

    //     let actual = fixture.get_matching_entry("second");
    //     let expected = vec!["second entry".to_string()];
    //     assert_eq!(actual, expected);
    // }

    // #[test]
    // fn test_get_matching_entries_case_insensitive() {
    //     let fixture = create_test_history();

    //     let actual = fixture.get_matching_entry("SECOND");
    //     let expected = vec!["second entry".to_string()];
    //     assert_eq!(actual, expected);
    // }

    // #[test]
    // fn test_get_matching_entries_no_matches() {
    //     let fixture = create_test_history();

    //     let actual = fixture.get_matching_entry("nonexistent");
    //     let expected: Vec<String> = vec![];
    //     assert_eq!(actual, expected);
    // }

    #[test]
    fn test_navigate_previous_from_start() {
        let mut fixture = create_test_history();

        let actual = fixture.navigate_previous();
        let expected = Some("third entry".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_previous_multiple_times() {
        let mut fixture = create_test_history();
        fixture.navigate_previous(); // "third entry"

        let actual = fixture.navigate_previous();
        let expected = Some("second entry".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_previous_at_end() {
        let mut fixture = create_test_history();
        fixture.navigate_previous(); // "third entry"
        fixture.navigate_previous(); // "second entry"
        fixture.navigate_previous(); // "first entry"

        let actual = fixture.navigate_previous(); // Should stay at "first entry"
        let expected = Some("first entry".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_next_from_middle() {
        let mut fixture = create_test_history();
        fixture.navigate_previous(); // "third entry"
        fixture.navigate_previous(); // "second entry"

        let actual = fixture.navigate_next();
        let expected = Some("third entry".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_next_to_clear() {
        let mut fixture = create_test_history();
        fixture.navigate_previous(); // "third entry"

        let actual = fixture.navigate_next();
        let expected = Some("".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_next_when_not_navigating() {
        let mut fixture = create_test_history();

        let actual = fixture.navigate_next();
        let expected = None;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_reset_navigation() {
        let mut fixture = create_test_history();
        fixture.navigate_previous();
        fixture.reset_navigation();

        let actual = fixture.current_entry();
        let expected = None;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_current_entry_when_navigating() {
        let mut fixture = create_test_history();
        fixture.navigate_previous();

        let actual = fixture.current_entry();
        let expected = Some("third entry".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_current_entry_when_not_navigating() {
        let fixture = create_test_history();

        let actual = fixture.current_entry();
        let expected = None;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_clear_removes_all_entries() {
        let mut fixture = create_test_history();
        fixture.clear();

        let actual = fixture.is_empty();
        let expected = true;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_len_returns_correct_count() {
        let fixture = create_test_history();

        let actual = fixture.len();
        let expected = 3;
        assert_eq!(actual, expected);
    }
    #[test]
    fn test_get_matching_entry_returns_most_recent() {
        let mut fixture = History::new(10);
        fixture.add_entry("test command 1".to_string());
        fixture.add_entry("test command 2".to_string());
        fixture.add_entry("other command".to_string());
        fixture.add_entry("test command 3".to_string()); // Most recent

        let actual = fixture.get_matching_entry("test");
        let expected = Some((0, "test command 3".to_string())); // Should return most recent
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_get_matching_entry_with_empty_prefix() {
        let fixture = create_test_history();

        let actual = fixture.get_matching_entry("");
        let expected = Some((0, "third entry".to_string())); // Most recent entry
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_get_matching_entry_prefers_recent_over_older() {
        let mut fixture = History::new(10);
        fixture.add_entry("test old command".to_string());
        fixture.add_entry("different command".to_string());
        fixture.add_entry("test newer command".to_string());
        fixture.add_entry("test most recent command".to_string()); // Most recent

        let actual = fixture.get_matching_entry("test");
        let expected = Some((0, "test most recent command".to_string())); // Should return most recent, not oldest
        assert_eq!(actual, expected);
    }
}
