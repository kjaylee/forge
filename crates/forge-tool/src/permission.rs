use std::sync::Arc;
use tokio::sync::RwLock;

use crate::{
    transport::{Message, Transport},
    ToolTrait,
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct PermissionRequest {
    pub action: String,
    pub context: Option<String>,
    pub request_id: String,
}

impl Message for PermissionRequest {
    fn get_id(&self) -> String {
        self.request_id.clone()
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct PermissionResponse {
    pub request_id: String,
    pub granted: bool,
}

impl Message for PermissionResponse {
    fn get_id(&self) -> String {
        self.request_id.clone()
    }
}

#[derive(Clone)]
pub struct Permission {
    transport: Arc<RwLock<Transport<PermissionRequest, PermissionResponse>>>,
}

impl Permission {
    pub fn new(transport: Transport<PermissionRequest, PermissionResponse>) -> Self {
        Self { transport: Arc::new(RwLock::new(transport)) }
    }
}

#[async_trait::async_trait]
impl ToolTrait for Permission {
    type Input = PermissionRequest;
    type Output = PermissionResponse;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let mut transport = self.transport.write().await;
        transport.send_and_receive(input).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::sync::mpsc;
    use uuid::Uuid;

    #[tokio::test]
    async fn test_permission_request_response() {
        // Create channels for the test
        let (event_tx, mut event_rx) = mpsc::unbounded_channel();
        let (response_tx, response_rx) = mpsc::unbounded_channel();

        // Create the permission tool
        let permission = Permission::new(Transport::new(event_tx, response_rx));

        // Spawn a task to simulate the server handling the request
        let handle = tokio::spawn(async move {
            // Wait for the request
            if let Some(request) = event_rx.recv().await {
                // Verify request fields
                assert_eq!(request.action, "delete_file");
                assert_eq!(request.context, Some("test file".to_string()));

                // Send back a response
                response_tx
                    .send(PermissionResponse { request_id: request.request_id, granted: true })
                    .unwrap();
            }
        });

        // Create a test request
        let request = PermissionRequest {
            action: "delete_file".to_string(),
            context: Some("test file".to_string()),
            request_id: Uuid::new_v4().to_string(),
        };

        // Send the request and wait for response
        let request_id = request.request_id.clone();
        let response = permission.call(request).await.unwrap();

        // Verify the response
        assert_eq!(response.request_id, request_id);
        assert!(response.granted);

        // Wait for the handler to complete
        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_permission_multiple_requests() {
        let (event_tx, mut event_rx) = mpsc::unbounded_channel();
        let (response_tx, response_rx) = mpsc::unbounded_channel();
        let permission = Permission::new(Transport::new(event_tx, response_rx));

        // Spawn response handler
        let handle = tokio::spawn(async move {
            let mut count = 0;
            while let Some(request) = event_rx.recv().await {
                count += 1;
                response_tx
                    .send(PermissionResponse {
                        request_id: request.request_id,
                        granted: count % 2 == 0, // Alternate between true and false
                    })
                    .unwrap();

                if count >= 3 {
                    break;
                }
            }
        });

        // Send multiple requests
        let mut responses = Vec::new();
        for i in 0..3 {
            let request = PermissionRequest {
                action: format!("action_{}", i),
                context: Some(format!("context_{}", i)),
                request_id: Uuid::new_v4().to_string(),
            };

            let response = permission.call(request.clone()).await.unwrap();
            responses.push((request, response));
        }

        // Verify responses
        for (i, (request, response)) in responses.iter().enumerate() {
            assert_eq!(response.request_id, request.request_id);
            assert_eq!(response.granted, (i + 1) % 2 == 0);
        }

        handle.await.unwrap();
    }
}
