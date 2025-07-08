use ratatui::buffer::Buffer;
use ratatui::layout::Rect;
use ratatui::style::{Color, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{StatefulWidget, Widget};

use crate::domain::{EditorStateExt, State};

/// Autocomplete widget for showing inline history suggestions
#[derive(Debug, PartialEq)]
pub struct AutocompleteWidget;

impl AutocompleteWidget {
    /// Check if autocomplete should be shown
    pub fn should_show(state: &State) -> bool {
        // Show autocomplete when:
        // 1. Not in spotlight mode
        // 2. Editor is in insert mode
        // 3. There are history entries that match current input
        // 4. Current input is not empty
        !state.spotlight.is_visible
            && state.editor.mode == edtui::EditorMode::Insert
            && !state.history.is_empty()
            && !state.editor.get_text().is_empty()
    }

    /// Get the suggestion text to display inline
    pub fn get_suggestion(state: &State) -> Option<(usize, String)> {
        if !Self::should_show(state) {
            return None;
        }

        let current_text = state.editor.get_text();
        if let Some((index, full_match)) = state.history.get_matching_entry(&current_text) {
            // Return only the completion part (suffix after current input)
            if full_match.len() > current_text.len() {
                let completion = &full_match[current_text.len()..];
                Some((index, completion.to_string()))
            } else {
                None // Full match, no completion needed
            }
        } else {
            None
        }
    }
}

impl StatefulWidget for AutocompleteWidget {
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State)
    where
        Self: Sized,
    {
        if let Some((index, suggestion)) = Self::get_suggestion(state) {
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
            let display_text = if suggestion.len() > available_width as usize {
                &suggestion[..available_width as usize]
            } else {
                &suggestion
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

            state.history.set_current_position(Some(index));
            Widget::render(suggestion_line, suggestion_area, buf);
        } else {
            state.history.set_current_position(None);
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
        let expected = Some((1, "ond command".to_string())); // "sec" + "ond command" = "second command"
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

    // #[test]
    // fn test_from_state_returns_widget_when_suggestion_available() {
    //     let fixture = create_test_state_with_history();

    //     let actual = AutocompleteWidget::from_state(&fixture);
    //     assert!(actual.is_some());

    //     let widget = actual.unwrap();
    //     assert_eq!(widget.suggestion, "ond command");
    //     assert_eq!(widget.cursor_col, 3); // cursor after "sec"
    // }

    // #[test]
    // fn test_from_state_returns_none_when_no_suggestion() {
    //     let mut fixture = create_test_state_with_history();
    //     fixture.editor.set_text_insert_mode("xyz".to_string());

    //     let actual = AutocompleteWidget::from_state(&fixture);
    //     let expected = None;
    //     assert_eq!(actual, expected);
    // }

    // #[test]
    // fn test_new_creates_widget_with_correct_fields() {
    //     let suggestion = "test suggestion".to_string();
    //     let cursor_col = 5;

    //     let actual = AutocompleteWidget::new(suggestion.clone(), cursor_col);

    //     assert_eq!(actual.suggestion, suggestion);
    //     assert_eq!(actual.cursor_col, cursor_col);
    // }
}
