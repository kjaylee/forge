use serde::Serialize;

use crate::{Event, ToolCallFull, ToolResult, Usage};

/// Events that are emitted by the agent for external consumption. This includes
/// events for all internal state changes.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ChatResponse {
    Text(String),
    ToolCallStart(ToolCallFull),
    ToolCallEnd(ToolResult),
    Usage(Usage),
    Event(Event),
    /// Represents a retry attempt due to a retriable error
    Retry {
        /// The error that caused the retry
        reason: String,
        /// The current attempt number (1-based)
        attempt: usize,
        /// The maximum number of attempts allowed
        max_attempts: usize,
    },
}
