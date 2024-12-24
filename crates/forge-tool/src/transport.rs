use serde::{de::DeserializeOwned, Serialize};
use tokio::sync::mpsc;

/// Trait for messages that can be sent through a transport
pub trait Message: Serialize + DeserializeOwned + Send {
    fn get_id(&self) -> String;
}

/// A generic transport that can send requests and receive responses
pub struct Transport<Req, Resp>
where
    Req: Message,
    Resp: Message,
{
    sender: mpsc::UnboundedSender<Req>,
    receiver: mpsc::UnboundedReceiver<Resp>,
}

impl<Req, Resp> Transport<Req, Resp>
where
    Req: Message,
    Resp: Message,
{
    /// Creates a new transport instance
    pub fn new(
        sender: mpsc::UnboundedSender<Req>,
        receiver: mpsc::UnboundedReceiver<Resp>,
    ) -> Self {
        Self { sender, receiver }
    }

    /// Sends a request and waits for a matching response
    pub async fn send_and_receive(&mut self, request: Req) -> Result<Resp, String> {
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
