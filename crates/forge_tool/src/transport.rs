use serde::{de::DeserializeOwned, Serialize};
use tokio::sync::broadcast::Sender;

/// Trait for messages that can be sent through a transport
pub trait Message: Serialize + DeserializeOwned + Send {
    fn get_id(&self) -> String;
}

// TODO: remove this once we have typesafe events.
impl Message for serde_json::Value {
    fn get_id(&self) -> String {
        self["request_id"].as_str().unwrap().to_string()
    }
}

#[derive(Clone)]
/// A generic transport that can send requests and receive responses
pub struct Transport {
    pub event_sender: Sender<serde_json::Value>,
    pub event_response_sender: Sender<serde_json::Value>,
}

impl Transport {
    /// Creates a new transport instance
    pub fn new(
        sender: Sender<serde_json::Value>,
        event_response_sender: Sender<serde_json::Value>,
    ) -> Self {
        Self { event_sender: sender, event_response_sender }
    }

    /// Sends a request and waits for a matching response
    pub async fn send_and_receive(
        &mut self,
        request: serde_json::Value,
    ) -> Result<serde_json::Value, String> {
        let request_id = request.get_id();
        // Send the request
        self.event_sender
            .send(request)
            .map_err(|e| format!("Failed to send: {}", e))?;

        // Wait for matching response
        while let Ok(response) = self.event_response_sender.subscribe().recv().await {
            if response.get_id() == request_id {
                return Ok(response);
            }
        }

        Err("Channel closed".to_string())
    }
}
