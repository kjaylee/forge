use forge_api::{ChatResponse, ConversationId};
use ratatui::crossterm::event::Event;

use crate::domain::{CancelId, Timer};

/// Top-level application actions that wrap route-specific actions
#[derive(Clone, Debug)]
pub enum Action {
    CrossTerm(Event),
    Initialize,
    Workspace {
        current_dir: Option<String>,
        current_branch: Option<String>,
    },
    ChatResponse(ChatResponse, Option<u64>), // Added spinner_id
    ConversationInitialized(ConversationId),
    IntervalTick(Timer),
    InterruptStream(Option<u64>),       // Added spinner_id
    StartStream(CancelId, Option<u64>), // Added spinner_id
    #[allow(dead_code)]
    Cancelled(CancelId),
}
