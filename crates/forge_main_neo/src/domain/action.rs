use derive_more::From;
use forge_api::ChatResponse;
use ratatui::crossterm::event::Event;

use crate::domain::Timer;

/// Top-level application actions that wrap route-specific actions
#[derive(Clone, From, Debug)]
pub enum Action {
    CrossTerm(Event),
    Initialize,
    Workspace {
        current_dir: Option<String>,
        current_branch: Option<String>,
    },
    ChatResponse(ChatResponse),
    IntervalTick(Timer),
}
