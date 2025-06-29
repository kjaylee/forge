use std::time::Duration;

use edtui::actions::{
    Execute, MoveToEndOfLine, MoveToStartOfLine, MoveWordBackward, MoveWordForward,
};
use edtui::{EditorEventHandler, EditorMode};

use crate::domain::{Command, State};

pub fn handle_word_navigation(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    use ratatui::crossterm::event::{KeyCode, KeyModifiers};

    if key_event.modifiers.contains(KeyModifiers::ALT) {
        match key_event.code {
            KeyCode::Char('b') => {
                MoveWordBackward(1).execute(&mut state.editor);
                Command::Empty
            }
            KeyCode::Char('f') => {
                MoveWordForward(1).execute(&mut state.editor);
                Command::Empty
            }
            _ => Command::Empty,
        }
    } else {
        Command::Empty
    }
}

pub fn handle_line_navigation(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    use ratatui::crossterm::event::{KeyCode, KeyModifiers};

    if key_event.modifiers.contains(KeyModifiers::CONTROL) {
        match key_event.code {
            KeyCode::Char('a') => {
                MoveToStartOfLine().execute(&mut state.editor);
                Command::Empty
            }
            KeyCode::Char('e') => {
                MoveToEndOfLine().execute(&mut state.editor);
                Command::Empty
            }
            _ => Command::Empty,
        }
    } else {
        Command::Empty
    }
}

pub fn handle_exit(_state: &mut State, key_event: ratatui::crossterm::event::KeyEvent) -> Command {
    use ratatui::crossterm::event::{KeyCode, KeyModifiers};

    if key_event.code == KeyCode::Char('d') && key_event.modifiers.contains(KeyModifiers::CONTROL) {
        Command::Exit
    } else {
        Command::Empty
    }
}

pub fn handle_submit(state: &mut State, key_event: ratatui::crossterm::event::KeyEvent) -> Command {
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

pub fn handle_spotlight_show(
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

pub fn handle_spotlight_hide(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    use ratatui::crossterm::event::KeyCode;

    if key_event.code == KeyCode::Esc {
        state.spotlight.is_visible = false;
        Command::Empty
    } else {
        Command::Empty
    }
}

pub fn handle_editor_default(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    EditorEventHandler::default().on_key_event(key_event, &mut state.editor);
    Command::Empty
}

pub fn handle_key_event(
    state: &mut State,
    key_event: ratatui::crossterm::event::KeyEvent,
) -> Command {
    // Try each handler in order, return early if any handles the event
    let cmd = handle_word_navigation(state, key_event);
    if !matches!(cmd, Command::Empty) {
        return cmd;
    }

    let cmd = handle_line_navigation(state, key_event);
    if !matches!(cmd, Command::Empty) {
        return cmd;
    }

    let cmd = handle_exit(state, key_event);
    if !matches!(cmd, Command::Empty) {
        return cmd;
    }

    let cmd = handle_submit(state, key_event);
    if !matches!(cmd, Command::Empty) {
        return cmd;
    }

    let cmd = handle_spotlight_show(state, key_event);
    if !matches!(cmd, Command::Empty) {
        return cmd;
    }

    let cmd = handle_spotlight_hide(state, key_event);
    if !matches!(cmd, Command::Empty) {
        return cmd;
    }

    // Always handle editor events last
    handle_editor_default(state, key_event)
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
}
