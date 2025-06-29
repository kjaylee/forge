use std::time::Duration;

use edtui::{EditorEventHandler, EditorMode};

use crate::domain::{Action, Command, State};

pub fn update(state: &mut State, action: impl Into<Action>) -> Command {
    let action = action.into();
    match &action {
        Action::Initialize => Command::ReadWorkspace,
        Action::Workspace { current_dir, current_branch } => {
            // TODO: can simply get workspace object from the action
            state.workspace.current_dir = current_dir.clone();
            state.workspace.current_branch = current_branch.clone();
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
                        return Command::Interval { duration: Some(Duration::from_millis(100)) }
                            .and_then(Command::ChatMessage(message));
                    }
                }

                // Editor
                EditorEventHandler::default().on_key_event(*key_event, &mut state.editor_state);

                Command::Empty
            }
            ratatui::crossterm::event::Event::Mouse(_) => Command::Empty,
            ratatui::crossterm::event::Event::Paste(_) => Command::Empty,
            ratatui::crossterm::event::Event::Resize(_, _) => Command::Empty,
        },
        Action::ChatResponse { message } => {
            state.add_assistant_message(message.clone());
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
