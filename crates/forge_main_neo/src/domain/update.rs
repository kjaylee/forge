use std::time::Duration;

use edtui::actions::{
    Execute, MoveToEndOfLine, MoveToStartOfLine, MoveWordBackward, MoveWordForward,
};
use edtui::{EditorEventHandler, EditorMode};
use forge_api::ChatResponse;

use crate::domain::{Action, Command, State};

pub fn update(state: &mut State, action: impl Into<Action>) -> Command {
    let action = action.into();
    match action {
        Action::Initialize => Command::ReadWorkspace,
        Action::Workspace { current_dir, current_branch } => {
            // TODO: can simply get workspace object from the action
            state.workspace.current_dir = current_dir;
            state.workspace.current_branch = current_branch;
            Command::Empty
        }
        Action::CrossTerm(event) => match event {
            ratatui::crossterm::event::Event::FocusGained => Command::Empty,
            ratatui::crossterm::event::Event::FocusLost => Command::Empty,
            ratatui::crossterm::event::Event::Key(key_event) => {
                // Handle EXIT events first
                use ratatui::crossterm::event::{KeyCode, KeyModifiers};
                let ctrl = key_event.modifiers.contains(KeyModifiers::CONTROL);
                let shift = key_event.modifiers.contains(KeyModifiers::SHIFT);
                let alt = key_event.modifiers.contains(KeyModifiers::ALT);

                // macOS: Option + Left/Right for word navigation
                if alt {
                    match key_event.code {
                        KeyCode::Char('b') => {
                            MoveWordBackward(1).execute(&mut state.editor_state);
                            return Command::Empty;
                        }
                        KeyCode::Char('f') => {
                            MoveWordForward(1).execute(&mut state.editor_state);
                            return Command::Empty;
                        }
                        _ => {}
                    }
                }

                // macOS: Command + Left/Right for line start/end navigation
                if ctrl {
                    match key_event.code {
                        KeyCode::Char('a') => {
                            MoveToStartOfLine().execute(&mut state.editor_state);
                            return Command::Empty;
                        }
                        KeyCode::Char('e') => {
                            MoveToEndOfLine().execute(&mut state.editor_state);
                            return Command::Empty;
                        }
                        _ => {}
                    }
                }

                // Handle EXIT events and other special keys

                // Switching TAB
                if key_event.code == KeyCode::Tab && !shift {
                    state.navigate_next();
                    state.current_route = state.current_route.clone();
                    return Command::Empty;
                }

                // Switching TAB (back)
                if key_event.code == KeyCode::BackTab || (key_event.code == KeyCode::Tab && shift) {
                    state.navigate_previous();
                    state.current_route = state.current_route.clone();
                    return Command::Empty;
                }

                // Exit
                if key_event.code == KeyCode::Char('d') && ctrl {
                    return Command::Exit;
                }

                // Submit
                if key_event.code == KeyCode::Enter && state.editor_state.mode == EditorMode::Normal
                {
                    let message = state.take_lines().join("\n");
                    state.add_user_message(message.clone());
                    if message.trim().is_empty() {
                        return Command::Empty;
                    } else {
                        state.show_spinner = true;
                        return Command::Interval { duration: Duration::from_millis(100) }
                            .and(Command::ChatMessage(message));
                    }
                }

                // Editor
                EditorEventHandler::default().on_key_event(key_event, &mut state.editor_state);

                Command::Empty
            }
            ratatui::crossterm::event::Event::Mouse(_) => Command::Empty,
            ratatui::crossterm::event::Event::Paste(_) => Command::Empty,
            ratatui::crossterm::event::Event::Resize(_, _) => Command::Empty,
        },
        Action::ChatResponse(response) => {
            if let ChatResponse::Text { ref text, is_complete, .. } = response
                && is_complete
                && !text.trim().is_empty()
            {
                state.show_spinner = false
            }
            state.add_assistant_message(response);
            if let Some(ref time) = state.timer
                && !state.show_spinner
            {
                let id = time.id.clone();
                state.timer = None;
                return Command::ClearInterval { id };
            }
            Command::Empty
        }
        Action::IntervalTick(timer) => {
            state.spinner.calc_next();
            // For now, interval ticks don't trigger any state changes or commands
            // This could be extended to update a timer display or trigger other actions
            state.timer = Some(timer.to_owned());
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
    use crate::domain::{Action, State};

    fn create_test_state_with_text() -> State {
        let mut state = State::default();
        // Set up some text content for testing cursor movement
        state.editor_state =
            EditorState::new(Lines::from("hello world this is a test\nsecond line here"));
        // Position cursor in the middle of the first word for testing
        state.editor_state.cursor = Index2::new(0, 6); // After "hello "
        state
    }

    #[test]
    fn test_macos_option_left_moves_word_backward() {
        let mut state = create_test_state_with_text();
        let initial_cursor = state.editor_state.cursor;
        let key_event = KeyEvent::new(KeyCode::Char('b'), KeyModifiers::ALT);
        let action = Action::CrossTerm(ratatui::crossterm::event::Event::Key(key_event));

        let actual_command = update(&mut state, action);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved backward to the beginning of the previous word
        assert!(state.editor_state.cursor.col < initial_cursor.col);
    }

    #[test]
    fn test_macos_option_right_moves_word_forward() {
        let mut state = create_test_state_with_text();
        let initial_cursor = state.editor_state.cursor;
        let key_event = KeyEvent::new(KeyCode::Char('f'), KeyModifiers::ALT);
        let action = Action::CrossTerm(ratatui::crossterm::event::Event::Key(key_event));

        let actual_command = update(&mut state, action);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should have moved forward to the beginning of the next word
        assert!(state.editor_state.cursor.col > initial_cursor.col);
    }

    #[test]
    fn test_macos_cmd_left_moves_to_line_start() {
        let mut state = create_test_state_with_text();
        let key_event = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::CONTROL);
        let action = Action::CrossTerm(ratatui::crossterm::event::Event::Key(key_event));

        let actual_command = update(&mut state, action);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should be at the beginning of the line
        assert_eq!(state.editor_state.cursor.col, 0);
    }

    #[test]
    fn test_macos_cmd_right_moves_to_line_end() {
        let mut state = create_test_state_with_text();
        let initial_row = state.editor_state.cursor.row;
        let key_event = KeyEvent::new(KeyCode::Char('e'), KeyModifiers::CONTROL);
        let action = Action::CrossTerm(ratatui::crossterm::event::Event::Key(key_event));

        let actual_command = update(&mut state, action);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Cursor should be at the end of the current line
        // The first line is "hello world this is a test" (25 characters, 0-indexed so
        // position 25)
        assert_eq!(state.editor_state.cursor.row, initial_row);
        assert_eq!(state.editor_state.cursor.col, 25);
    }

    #[test]
    fn test_regular_arrow_keys_still_work() {
        let mut state = create_test_state_with_text();
        let _initial_cursor = state.editor_state.cursor;
        let key_event = KeyEvent::new(KeyCode::Left, KeyModifiers::NONE);
        let action = Action::CrossTerm(ratatui::crossterm::event::Event::Key(key_event));

        let actual_command = update(&mut state, action);
        let expected_command = Command::Empty;

        assert_eq!(actual_command, expected_command);
        // Regular arrow keys should pass through to the editor
        // The cursor position might change due to normal editor handling
        // We just verify the command was processed normally
    }
}
