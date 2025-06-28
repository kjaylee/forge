use ratatui::layout::Rect;
use ratatui::style::{Color, Style};
use ratatui::widgets::{Clear, Widget};

/// Represents an individual autocomplete command option
#[derive(Clone, Debug, PartialEq)]
pub struct AutocompleteOption {
    pub name: String,
    pub description: String,
}

impl AutocompleteOption {
    pub fn new(name: impl Into<String>, description: impl Into<String>) -> Self {
        Self { name: name.into(), description: description.into() }
    }
}

/// Autocomplete widget with embedded state
#[derive(Clone, Debug)]
pub struct AutoComplete {
    pub is_active: bool,
    pub selected_index: usize,
    pub filter_text: String,
    pub available_commands: Vec<AutocompleteOption>,
    pub filtered_commands: Vec<AutocompleteOption>,
}

impl Default for AutoComplete {
    fn default() -> Self {
        let available_commands = vec![
            AutocompleteOption::new("foo", "Execute foo command"),
            AutocompleteOption::new("bar", "Execute bar command"),
            AutocompleteOption::new("baz", "Execute baz command"),
        ];

        Self {
            is_active: false,
            selected_index: 0,
            filter_text: String::new(),
            filtered_commands: available_commands.clone(),
            available_commands,
        }
    }
}

impl AutoComplete {
    pub fn activate(&mut self, filter_text: String) {
        self.is_active = true;
        self.filter_text = filter_text;
        self.selected_index = 0;
        self.update_filtered_commands();
    }

    pub fn deactivate(&mut self) {
        self.is_active = false;
        self.filter_text.clear();
        self.selected_index = 0;
        self.filtered_commands = self.available_commands.clone();
    }

    pub fn update_filter(&mut self, filter_text: String) {
        self.filter_text = filter_text;
        self.selected_index = 0;
        self.update_filtered_commands();
    }

    fn update_filtered_commands(&mut self) {
        self.filtered_commands = self
            .available_commands
            .iter()
            .filter(|cmd| cmd.name.contains(&self.filter_text))
            .cloned()
            .collect();
    }

    pub fn select_next(&mut self) {
        if !self.filtered_commands.is_empty() {
            self.selected_index = (self.selected_index + 1) % self.filtered_commands.len();
        }
    }

    pub fn select_previous(&mut self) {
        if !self.filtered_commands.is_empty() {
            self.selected_index = if self.selected_index == 0 {
                self.filtered_commands.len() - 1
            } else {
                self.selected_index - 1
            };
        }
    }

    pub fn get_selected_command(&self) -> Option<&AutocompleteOption> {
        self.filtered_commands.get(self.selected_index)
    }
}

/// Autocomplete popup widget
pub struct AutocompletePopup<'a> {
    autocomplete: &'a AutoComplete,
    area: Rect,
    user_area: Rect,
}

impl<'a> AutocompletePopup<'a> {
    pub fn new(autocomplete: &'a AutoComplete, area: Rect, user_area: Rect) -> Self {
        Self { autocomplete, area, user_area }
    }
}

impl<'a> Widget for AutocompletePopup<'a> {
    fn render(self, _area: Rect, buf: &mut ratatui::prelude::Buffer)
    where
        Self: Sized,
    {
        if !self.autocomplete.is_active || self.autocomplete.filtered_commands.is_empty() {
            return;
        }

        // Calculate popup position (above the user input area) - no borders needed
        let popup_height = (self.autocomplete.filtered_commands.len() as u16).min(5);
        let popup_area = Rect {
            x: self.area.x + 1,
            y: self.user_area.y.saturating_sub(popup_height), // Position above the user input area
            width: self.area.width.saturating_sub(2).min(40),
            height: popup_height,
        };

        // Clear the popup area before rendering
        Clear.render(popup_area, buf);

        for (i, command) in self.autocomplete.filtered_commands.iter().enumerate() {
            if i >= popup_area.height as usize {
                break;
            }

            let y = popup_area.y + i as u16;
            let style = if i == self.autocomplete.selected_index {
                Style::default().bg(Color::White)
            } else {
                Style::default()
            };

            let command_text = format!("/{} - {}", command.name, command.description);
            let truncated_text = if command_text.len() > popup_area.width as usize {
                format!(
                    "{}...",
                    &command_text[..popup_area.width.saturating_sub(3) as usize]
                )
            } else {
                command_text
            };

            for (j, ch) in truncated_text.chars().enumerate() {
                if j >= popup_area.width as usize {
                    break;
                }
                let cell = buf.cell_mut((popup_area.x + j as u16, y)).unwrap();
                cell.set_char(ch);
                cell.set_style(style);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_autocomplete_option_creation() {
        let fixture = AutocompleteOption::new("test", "Test command");
        let actual = fixture;
        let expected = AutocompleteOption {
            name: "test".to_string(),
            description: "Test command".to_string(),
        };
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_autocomplete_new() {
        let fixture = AutoComplete::default();
        let actual = fixture.available_commands.len();
        let expected = 3;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_autocomplete_filtering() {
        let mut fixture = AutoComplete::default();
        fixture.update_filter("fo".to_string());
        let actual = fixture.filtered_commands.len();
        let expected = 1; // Only "foo" should match
        assert_eq!(actual, expected);
        assert_eq!(fixture.filtered_commands[0].name, "foo");
    }

    #[test]
    fn test_autocomplete_navigation() {
        let mut fixture = AutoComplete::default();
        fixture.activate("".to_string());

        // Test next selection
        fixture.select_next();
        let actual = fixture.selected_index;
        let expected = 1;
        assert_eq!(actual, expected);

        // Test previous selection
        fixture.select_previous();
        let actual = fixture.selected_index;
        let expected = 0;
        assert_eq!(actual, expected);

        // Test wrap around
        fixture.select_previous();
        let actual = fixture.selected_index;
        let expected = 2; // Should wrap to last item
        assert_eq!(actual, expected);
    }
}
