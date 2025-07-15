use std::collections::VecDeque;

/// Command history with LRU storage and navigation tracking
#[derive(Clone, Debug)]
pub struct CommandHistory {
    commands: VecDeque<String>,
    current_index: Option<usize>,
    max_size: usize,
}

impl Default for CommandHistory {
    fn default() -> Self {
        Self {
            commands: VecDeque::new(),
            current_index: None,
            max_size: 100,
        }
    }
}

impl CommandHistory {
    /// Add a command to history (LRU - most recent at front)
    pub fn add_command(&mut self, command: String) {
        // Remove existing instance if present
        if let Some(pos) = self.commands.iter().position(|c| c == &command) {
            self.commands.remove(pos);
        }

        // Add to front
        self.commands.push_front(command);

        // Enforce size limit
        if self.commands.len() > self.max_size {
            self.commands.pop_back();
        }

        // Reset navigation
        self.current_index = None;
    }

    /// Navigate to previous command (up arrow)
    pub fn navigate_up(&mut self) -> Option<String> {
        if self.commands.is_empty() {
            return None;
        }

        match self.current_index {
            None => {
                // Start navigation from most recent
                self.current_index = Some(0);
                self.commands.front().cloned()
            }
            Some(index) => {
                // Move to older command if possible
                if index + 1 < self.commands.len() {
                    self.current_index = Some(index + 1);
                    self.commands.get(index + 1).cloned()
                } else {
                    // Stay at oldest command
                    self.commands.get(index).cloned()
                }
            }
        }
    }

    /// Navigate to next command (down arrow)
    pub fn navigate_down(&mut self) -> Option<String> {
        match self.current_index {
            None => None,
            Some(0) => {
                // Reset to no selection (empty input)
                self.current_index = None;
                Some(String::new())
            }
            Some(index) => {
                // Move to newer command
                self.current_index = Some(index - 1);
                self.commands.get(index - 1).cloned()
            }
        }
    }

    /// Get autocomplete suggestion for current input
    pub fn get_autocomplete_suggestion(&self, current_input: &str) -> Option<String> {
        if current_input.trim().is_empty() {
            return None;
        }

        // Find first command that starts with current input
        self.commands
            .iter()
            .find(|cmd| cmd.starts_with(current_input) && cmd != &current_input)
            .cloned()
    }

    /// Reset navigation state (called when user types)
    pub fn reset_navigation(&mut self) {
        self.current_index = None;
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_add_command() {
        let mut fixture = CommandHistory::default();
        fixture.add_command("test command".to_string());

        let actual = fixture.commands.len();
        let expected = 1;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_up() {
        let mut fixture = CommandHistory::default();
        fixture.add_command("first".to_string());
        fixture.add_command("second".to_string());

        let actual = fixture.navigate_up();
        let expected = Some("second".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_navigate_down() {
        let mut fixture = CommandHistory::default();
        fixture.add_command("first".to_string());
        fixture.add_command("second".to_string());
        fixture.navigate_up(); // Navigate to "second"

        let actual = fixture.navigate_down();
        let expected = Some(String::new());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_autocomplete_suggestion() {
        let mut fixture = CommandHistory::default();
        fixture.add_command("test command".to_string());
        fixture.add_command("test another".to_string());

        let actual = fixture.get_autocomplete_suggestion("test");
        let expected = Some("test another".to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_lru_behavior() {
        let mut fixture = CommandHistory::default();
        fixture.add_command("first".to_string());
        fixture.add_command("second".to_string());
        fixture.add_command("first".to_string()); // Re-add first

        let actual = fixture.navigate_up();
        let expected = Some("first".to_string()); // Should be most recent
        assert_eq!(actual, expected);
    }
}
