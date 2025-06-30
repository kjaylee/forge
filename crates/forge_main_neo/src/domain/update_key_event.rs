use std::time::Duration;

use edtui::actions::{
    Execute, MoveToEndOfLine, MoveToStartOfLine, MoveWordBackward, MoveWordForward,
};
use edtui::{EditorEventHandler, EditorMode};
use ratatui::crossterm::event::{KeyCode, KeyModifiers};

use crate::domain::spotlight::SpotlightState;
use crate::domain::{Command, State};

fn handle_word_navigation(
    editor: &mut edtui::EditorState,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> bool {
    use ratatui::crossterm::event::{KeyCode, KeyModifiers};

    if key_event.modifiers.contains(KeyModifiers::ALT) {
        match key_event.code {
            KeyCode::Char('b') => {
                MoveWordBackward(1).execute(editor);
                true
            }
            KeyCode::Char('f') => {
                MoveWordForward(1).execute(editor);
                true
            }
            _ => false,
        }
    } else {
        false
    }
}

fn handle_line_navigation(
    editor: &mut edtui::EditorState,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> bool {
    use ratatui::crossterm::event::{KeyCode, KeyModifiers};

    if key_event.modifiers.contains(KeyModifiers::CONTROL) {
        match key_event.code {
            KeyCode::Char('a') => {
                MoveToStartOfLine().execute(editor);
                true
            }
            KeyCode::Char('e') => {
                MoveToEndOfLine().execute(editor);
                true
            }
            _ => false,
        }
    } else {
        false
    }
}

fn handle_prompt_submit(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    use ratatui::crossterm::event::KeyCode;

    if key_event.code == KeyCode::Enter && state.editor.mode == EditorMode::Normal {
        let message = state.take_lines().join("\n");
        state.add_user_message(message.clone());
        if message.trim().is_empty() {
            Command::Empty
        } else {
            state.show_spinner = true;
            Command::Interval { duration: Duration::from_millis(100) }
                .and(Command::ChatMessage(message))
        }
    } else {
        Command::Empty
    }
}

fn handle_spotlight_show(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    use ratatui::crossterm::event::KeyCode;

    if key_event.code == KeyCode::Char(':') && state.editor.mode == EditorMode::Normal {
        state.spotlight.is_visible = true;
        Command::Empty
    } else {
        Command::Empty
    }
}

fn handle_spotlight_hide(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    use ratatui::crossterm::event::KeyCode;

    if key_event.code == KeyCode::Esc {
        state.spotlight = SpotlightState::default();
        Command::Empty
    } else {
        Command::Empty
    }
}

fn handle_editor_default(
    editor: &mut edtui::EditorState,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    EditorEventHandler::default().on_key_event(key_event, editor);
    Command::Empty
}

pub fn handle_key_event(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    // Always handle exit regardless of spotlight state
    if key_event.code == KeyCode::Char('d') && key_event.modifiers.contains(KeyModifiers::CONTROL) {
        return Command::Exit;
    }

    if state.spotlight.is_visible {
        // When spotlight is visible, route events to spotlight editor
        let cmd = handle_spotlight_hide(state, key_event);

        // Check if navigation was handled first
        let line_nav_handled = handle_line_navigation(&mut state.spotlight.editor, key_event);
        let word_nav_handled = handle_word_navigation(&mut state.spotlight.editor, key_event);

        // Only call editor default if no navigation was handled
        let result_cmd = if !line_nav_handled && !word_nav_handled {
            let editor_cmd = handle_editor_default(&mut state.spotlight.editor, key_event);
            cmd.and(editor_cmd)
        } else {
            cmd
        };

        // Always keep spotlight in "insert" mode
        state.spotlight.editor.mode = EditorMode::Insert;

        result_cmd
    } else {
        // When spotlight is not visible, route events to main editor
        // Check if navigation was handled first
        let line_nav_handled = handle_line_navigation(&mut state.editor, key_event);
        let word_nav_handled = handle_word_navigation(&mut state.editor, key_event);

        // Only call editor default and spotlight show if no navigation was handled
        if !line_nav_handled && !word_nav_handled {
            handle_editor_default(&mut state.editor, key_event)
                .and(handle_spotlight_show(state, key_event))
                .and(handle_prompt_submit(state, key_event))
        } else {
            Command::Empty
        }
    }
}

#[cfg(test)]
mod tests {
    use edtui::{EditorState, Index2, Lines};
    use pretty_assertions::assert_eq;
    use ratatui::crossterm::event::{KeyCode, KeyEvent, KeyModifiers};

    use super::*;
    use crate::domain::State;

    fn create_test_state_with_text() -> State {
        let mut state = State::default();
        // Set up some text content for testing cursor movement
        state.editor =
            EditorState::new(Lines::from("hello world this is a test\nsecond line here"));
        // Position cursor in the middle of the first word for testing
        state.editor.cursor = Index2::new(0, 6); // After "hello "
        // Ensure spotlight is not visible for main editor tests
        state.spotlight.is_visible = false;
        state
    }

    #[test]
    fn test_macos_option_left_moves_word_backward() {
        let mut state = create_test_state_with_text();
        let initial_cursor = state.editor.cursor;
        let key_event = KeyEvent::new(KeyCode::Char('b'), KeyModifiers::ALT);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved backward to the beginning of the previous word
        assert!(state.editor.cursor.col < initial_cursor.col);
    }

    #[test]
    fn test_macos_option_right_moves_word_forward() {
        let mut state = create_test_state_with_text();
        let initial_cursor = state.editor.cursor;
        let key_event = KeyEvent::new(KeyCode::Char('f'), KeyModifiers::ALT);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved forward to the beginning of the next word
        assert!(state.editor.cursor.col > initial_cursor.col);
    }

    #[test]
    fn test_macos_cmd_left_moves_to_line_start() {
        let mut state = create_test_state_with_text();
        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::CONTROL);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should be at the beginning of the line
        assert_eq!(state.editor.cursor.col, 0);
    }

    #[test]
    fn test_macos_cmd_right_moves_to_line_end() {
        let mut state = create_test_state_with_text();
        let initial_row = state.editor.cursor.row;
        let key_event = KeyEvent::new(KeyCode::Char('e'), KeyModifiers::CONTROL);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should be at the end of the current line
        // The first line is "hello world this is a test" (25 characters, 0-indexed so
        // position 25)
        assert_eq!(state.editor.cursor.row, initial_row);
        assert_eq!(state.editor.cursor.col, 25);
    }

    #[test]
    fn test_regular_arrow_keys_still_work() {
        let mut state = create_test_state_with_text();
        let _initial_cursor = state.editor.cursor;
        let key_event = KeyEvent::new(KeyCode::Left, KeyModifiers::NONE);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Regular arrow keys should pass through to the editor
        // The cursor position might change due to normal editor handling
        // We just verify the command was processed normally
    }

    #[test]
    fn test_spotlight_visible_routes_events_to_spotlight_editor() {
        let mut state = create_test_state_with_text();
        state.spotlight.is_visible = true;
        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::CONTROL);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // When spotlight is visible, cursor movement should affect spotlight editor
        assert_eq!(state.spotlight.editor.cursor.col, 0);
        // Main editor cursor should remain unchanged
        assert_eq!(state.editor.cursor.col, 6);
    }

    #[test]
    fn test_spotlight_hidden_routes_events_to_main_editor() {
        let mut state = create_test_state_with_text();
        state.spotlight.is_visible = false;
        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::CONTROL);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // When spotlight is hidden, cursor movement should affect main editor
        assert_eq!(state.editor.cursor.col, 0);
        // Spotlight editor cursor should remain unchanged
        assert_eq!(state.spotlight.editor.cursor.col, 0);
    }

    #[test]
    fn test_escape_hides_spotlight_regardless_of_visibility() {
        let mut state = create_test_state_with_text();
        state.spotlight.is_visible = true;
        let key_event = KeyEvent::new(KeyCode::Esc, KeyModifiers::NONE);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        assert!(!state.spotlight.is_visible);
    }

    #[test]
    fn test_exit_command_works_regardless_of_spotlight_state() {
        let mut state = create_test_state_with_text();
        state.spotlight.is_visible = true;
        let key_event = KeyEvent::new(KeyCode::Char('d'), KeyModifiers::CONTROL);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Exit;

        assert_eq!(actual_command, expected_command);
    }

    #[test]
    fn test_spotlight_word_navigation() {
        let mut state = create_test_state_with_text();
        state.spotlight.is_visible = true;
        // Set up some text in spotlight editor
        state.spotlight.editor = EditorState::new(Lines::from("hello world test"));
        state.spotlight.editor.cursor = Index2::new(0, 6); // After "hello "
        let initial_cursor = state.spotlight.editor.cursor;
        let key_event = KeyEvent::new(KeyCode::Char('f'), KeyModifiers::ALT);

        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved forward in spotlight editor
        assert!(state.spotlight.editor.cursor.col > initial_cursor.col);
    }

    #[test]
    fn test_navigation_prevents_editor_default_and_spotlight_show() {
        let mut state = create_test_state_with_text();
        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::CONTROL);

        // Before the fix, this would have called editor_default and potentially
        // spotlight_show After the fix, navigation handling should
        // short-circuit these calls
        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved to line start (navigation was handled)
        assert_eq!(state.editor.cursor.col, 0);
        // Spotlight should remain hidden (spotlight_show was not called)
        assert!(!state.spotlight.is_visible);
    }

    #[test]
    fn test_word_navigation_prevents_editor_default_and_spotlight_show() {
        let mut state = create_test_state_with_text();
        let key_event = KeyEvent::new(KeyCode::Char('f'), KeyModifiers::ALT);

        // Before the fix, this would have called editor_default and potentially
        // spotlight_show After the fix, word navigation handling should
        // short-circuit these calls
        let actual_command = handle_key_event(&mut state, key_event);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved forward (navigation was handled)
        assert!(state.editor.cursor.col > 6); // Started at position 6
        // Spotlight should remain hidden (spotlight_show was not called)
        assert!(!state.spotlight.is_visible);
    }
}
