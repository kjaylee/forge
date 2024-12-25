use forge_tool::transport::Transport;
use serde_json::Value;
use tokio::sync::broadcast;

use crate::completion::Completion;

// Shared state between each request to the server
pub struct App {
    completion: Completion,
    pub(crate) transport: Transport,
}

impl App {
    pub fn new(path: impl Into<String>) -> Self {
        let (raw_event_sender, _) = broadcast::channel::<Value>(32);
        let (event_response_sender, _) = broadcast::channel::<Value>(32);
        Self {
            completion: Completion::new(path),
            transport: Transport::new(raw_event_sender, event_response_sender),
        }
    }
}
