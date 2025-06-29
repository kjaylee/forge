use derive_more::From;
use ratatui::crossterm::event::Event;

use crate::domain::Timer;

/// Top-level application actions that wrap route-specific actions
#[derive(Clone, From, Debug, PartialEq)]
pub enum Action {
    CrossTerm(Event),
    Initialize,
    Workspace {
        current_dir: Option<String>,
        current_branch: Option<String>,
    },
    ChatResponse {
        message: String,
    },
    IntervalTick(Timer),
}
