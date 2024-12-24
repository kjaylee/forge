use serde::{de::DeserializeOwned, Serialize};
use tokio::sync::mpsc;

/// Trait for messages that can be sent through a transport
pub trait Message: Serialize + DeserializeOwned + Send {
    fn get_id(&self) -> String;
}

impl Message for serde_json::Value {
    fn get_id(&self) -> String {
        self["request_id"].as_str().unwrap().to_string()
    }
}

/// A generic transport that can send requests and receive responses
pub struct Transport {
    sender: mpsc::UnboundedSender<serde_json::Value>,
    receiver: mpsc::UnboundedReceiver<serde_json::Value>,
}

impl Transport {
    /// Creates a new transport instance
    pub fn new(
        sender: mpsc::UnboundedSender<serde_json::Value>,
        receiver: mpsc::UnboundedReceiver<serde_json::Value>,
    ) -> Self {
        Self { sender, receiver }
    }

    /// Sends a request and waits for a matching response
    pub async fn send_and_receive(
        &mut self,
        request: serde_json::Value,
    ) -> Result<serde_json::Value, String> {
        let request_id = request.get_id();
        // Send the request
        self.sender
            .send(request)
            .map_err(|e| format!("Failed to send: {}", e))?;

        // Wait for matching response
        while let Some(response) = self.receiver.recv().await {
            if response.get_id() == request_id {
                return Ok(response);
            }
        }

        Err("Channel closed".to_string())
    }
}
