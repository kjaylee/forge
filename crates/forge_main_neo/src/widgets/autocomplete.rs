use ratatui::buffer::Buffer;
use ratatui::layout::Rect;
use ratatui::style::{Color, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{StatefulWidget, Widget};

use crate::domain::{EditorStateExt, State};

/// Autocomplete widget for showing inline history suggestions
/// 
/// This widget displays dimmed text suggestions based on command history.
/// It integrates with the History domain to provide intelligent autocompletion
/// that helps users quickly complete commands they've used before.
/// 
/// The widget follows these principles:
/// - Only shows suggestions in insert mode when not in spotlight
/// - Displays suggestions as dimmed text after the cursor
/// - Does not modify state during rendering (pure UI component)
/// - Provides completion text that can be applied via key events
#[derive(Debug, PartialEq)]
pub struct AutocompleteWidget;

/// Represents an autocomplete suggestion with metadata
#[derive(Debug, Clone, PartialEq)]
pub struct AutocompleteSuggestion {
    /// The text to complete the current input
    pub completion_text: String,
    /// The full matched entry from history
    pub full_match: String,
    /// Index in history for this suggestion
    pub history_index: usize,
}

impl AutocompleteWidget {
    /// Check if autocomplete should be shown
    /// 
    /// Returns true when all conditions are met:
    /// - Not in spotlight mode (spotlight takes precedence)
    /// - Editor is in insert mode (only show during text input)
    /// - History has entries to suggest from
    /// - Current input is not empty (need something to match against)
    pub fn should_show(state: &State) -> bool {
        !state.spotlight.is_visible
            && state.editor.mode == edtui::EditorMode::Insert
            && !state.history.is_empty()
            && !state.editor.get_text().is_empty()
    }

    /// Get the autocomplete suggestion for the current input
    /// 
    /// Returns a suggestion if one is available, or None if no suggestion
    /// should be shown. This method caches the matching logic to avoid
    /// redundant computations.
    pub fn get_suggestion(state: &State) -> Option<AutocompleteSuggestion> {
        if !Self::should_show(state) {
            return None;
        }

        let current_text = state.editor.get_text();
        if let Some((index, full_match)) = state.history.get_matching_entry(&current_text) {
            // Return only the completion part (suffix after current input)
            if full_match.len() > current_text.len() {
                let completion_text = full_match[current_text.len()..].to_string();
                Some(AutocompleteSuggestion {
                    completion_text,
                    full_match,
                    history_index: index,
                })
            } else {
                None // Full match, no completion needed
            }
        } else {
            None
        }
    }

    /// Apply the autocomplete suggestion to the editor
    /// 
    /// This is a helper method that can be called from key event handlers
    /// to complete the current input with the suggestion.
    pub fn apply_suggestion(state: &mut State) -> bool {
        if let Some(suggestion) = Self::get_suggestion(state) {
            let current_text = state.editor.get_text();
            let completed_text = format!("{current_text}{}", suggestion.completion_text);
            state.editor.set_text_insert_mode(completed_text);
            true
        } else {
            false
        }
    }
}

impl StatefulWidget for AutocompleteWidget {
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State)
    where
        Self: Sized,
    {
        if let Some(suggestion) = Self::get_suggestion(state) {
            let cursor_col = state.editor.cursor.col as u16;

            // Calculate position after the cursor
            let suggestion_x = area.x + cursor_col;
            let suggestion_y = area.y;

            // Make sure we don't go beyond the area bounds
            if suggestion_x >= area.x + area.width || suggestion_y >= area.y + area.height {
                return;
            }

            // Calculate how much of the suggestion we can display
            let available_width = (area.x + area.width).saturating_sub(suggestion_x);
            let display_text = if suggestion.completion_text.len() > available_width as usize {
                &suggestion.completion_text[..available_width as usize]
            } else {
                &suggestion.completion_text
            };

            // Create dimmed text spans
            let suggestion_line = Line::from(vec![Span::styled(
                display_text,
                Style::default().fg(Color::DarkGray),
            )]);

            // Render the suggestion at the cursor position
            let suggestion_area = Rect {
                x: suggestion_x,
                y: suggestion_y,
                width: display_text.len() as u16,
                height: 1,
            };

            Widget::render(suggestion_line, suggestion_area, buf);
        }
    }
}

#[cfg(test)]
mod tests {
    use edtui::EditorMode;
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::domain::EditorStateExt;

    fn create_test_state_with_history() -> State {
        let mut fixture = State::default();
        fixture.history.add_entry("first command".to_string());
        fixture.history.add_entry("second command".to_string());
        fixture.history.add_entry("third command".to_string());
        fixture.editor.mode = EditorMode::Insert;
        fixture.editor.set_text_insert_mode("sec".to_string());
        fixture
    }

    #[test]
    fn test_should_show_returns_true_when_conditions_met() {
        let fixture = create_test_state_with_history();

        let actual = AutocompleteWidget::should_show(&fixture);
        let expected = true;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_should_show_returns_false_when_spotlight_visible() {
        let mut fixture = create_test_state_with_history();
        fixture.spotlight.is_visible = true;

        let actual = AutocompleteWidget::should_show(&fixture);
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_should_show_returns_false_when_editor_not_insert_mode() {
        let mut fixture = create_test_state_with_history();
        fixture.editor.mode = EditorMode::Normal;

        let actual = AutocompleteWidget::should_show(&fixture);
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_should_show_returns_false_when_history_empty() {
        let mut fixture = create_test_state_with_history();
        fixture.history.clear();

        let actual = AutocompleteWidget::should_show(&fixture);
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_should_show_returns_false_when_no_input() {
        let mut fixture = create_test_state_with_history();
        fixture.editor.set_text_insert_mode("".to_string());

        let actual = AutocompleteWidget::should_show(&fixture);
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_get_suggestion_returns_completion() {
        let fixture = create_test_state_with_history();

        let actual = AutocompleteWidget::get_suggestion(&fixture);
        let expected = Some(AutocompleteSuggestion {
            completion_text: "ond command".to_string(),
            full_match: "second command".to_string(),
            history_index: 1,
        });
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_get_suggestion_returns_none_when_no_match() {
        let mut fixture = create_test_state_with_history();
        fixture.editor.set_text_insert_mode("xyz".to_string());

        let actual = AutocompleteWidget::get_suggestion(&fixture);
        let expected = None;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_get_suggestion_returns_none_when_full_match() {
        let mut fixture = create_test_state_with_history();
        fixture
            .editor
            .set_text_insert_mode("second command".to_string());

        let actual = AutocompleteWidget::get_suggestion(&fixture);
        let expected = None; // Full match, no completion needed
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_apply_suggestion_completes_text() {
        let mut fixture = create_test_state_with_history();

        let actual = AutocompleteWidget::apply_suggestion(&mut fixture);
        let expected = true;
        assert_eq!(actual, expected);
        assert_eq!(fixture.editor.get_text(), "second command");
    }

    #[test]
    fn test_apply_suggestion_returns_false_when_no_suggestion() {
        let mut fixture = create_test_state_with_history();
        fixture.editor.set_text_insert_mode("xyz".to_string());

        let actual = AutocompleteWidget::apply_suggestion(&mut fixture);
        let expected = false;
        assert_eq!(actual, expected);
        assert_eq!(fixture.editor.get_text(), "xyz"); // Unchanged
    }
}