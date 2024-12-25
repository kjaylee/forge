use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

use crate::transport::{Message, Transport};
use crate::ToolTrait;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct UserInputRequest {
    pub question: String,
    pub context: Option<String>,
    pub request_id: String,
}

impl Message for UserInputRequest {
    fn get_id(&self) -> String {
        self.request_id.clone()
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct UserInputResponse {
    pub answer: String,
    pub request_id: String,
}

impl Message for UserInputResponse {
    fn get_id(&self) -> String {
        self.request_id.clone()
    }
}

#[derive(Clone)]
pub struct UserInput {
    transport: Arc<RwLock<Transport>>,
}

impl UserInput {
    pub fn new(transport: Arc<RwLock<Transport>>) -> Self {
        Self { transport }
    }
}

#[async_trait::async_trait]
impl ToolTrait for UserInput {
    type Input = UserInputRequest;
    type Output = UserInputResponse;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        let input = serde_json::to_value(input).map_err(|e| e.to_string())?;
        let mut transport = self.transport.write().await;
        let response = transport.send_and_receive(input).await?;
        Ok(serde_json::from_value(response).map_err(|e| e.to_string())?)
    }
}

#[cfg(test)]
mod tests {
    use tokio::sync::broadcast;
    use uuid::Uuid;

    use super::*;

    #[tokio::test]
    async fn test_user_input_request_response() {
        // Create channels for the test
        let (event_tx, mut event_rx) = broadcast::channel(32);
        let (response_tx, _) = broadcast::channel(32);

        // Create the user input tool
        let user_input = UserInput::new(Arc::new(RwLock::new(Transport::new(
            event_tx,
            response_tx.clone(),
        ))));

        // Spawn a task to simulate the server handling the request
        let handle = tokio::spawn(async move {
            // Wait for the request
            if let Ok(request) = event_rx.recv().await {
                // Send back a response
                response_tx
                    .send(
                        serde_json::to_value(UserInputResponse {
                            request_id: request["request_id"].as_str().unwrap().to_string(),
                            answer: "John Doe".to_string(),
                        })
                        .unwrap(),
                    )
                    .unwrap();
            }
        });

        // Create a test request
        let request = UserInputRequest {
            question: "What is your name?".to_string(),
            context: Some("greeting".to_string()),
            request_id: Uuid::new_v4().to_string(),
        };

        // Send the request and wait for response
        let request_id = request.request_id.clone();
        let response = user_input.call(request).await.unwrap();

        // Verify the response
        assert_eq!(response.request_id, request_id);
        assert_eq!(response.answer, "John Doe");

        // Wait for the handler to complete
        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_user_input_multiple_requests() {
        let (event_tx, mut event_rx) = broadcast::channel(32);
        let (response_tx, _) = broadcast::channel(32);
        let user_input = UserInput::new(Arc::new(RwLock::new(Transport::new(
            event_tx,
            response_tx.clone(),
        ))));

        // Spawn response handler
        let handle = tokio::spawn(async move {
            let mut count = 0;
            while let Ok(request) = event_rx.recv().await {
                count += 1;
                response_tx
                    .send(
                        serde_json::to_value(UserInputResponse {
                            request_id: request["request_id"].as_str().unwrap().to_string(),
                            answer: format!("Answer {}", count),
                        })
                        .unwrap(),
                    )
                    .unwrap();

                if count >= 3 {
                    break;
                }
            }
        });

        // Send multiple requests
        let mut responses = Vec::new();
        for i in 0..3 {
            let request = UserInputRequest {
                question: format!("Question {}", i),
                context: Some(format!("Context {}", i)),
                request_id: Uuid::new_v4().to_string(),
            };

            let response = user_input.call(request.clone()).await.unwrap();
            responses.push((request, response));
        }

        // Verify responses
        for (i, (request, response)) in responses.iter().enumerate() {
            assert_eq!(response.request_id, request.request_id);
            assert_eq!(response.answer, format!("Answer {}", i + 1));
        }

        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_user_input_concurrent_requests() {
        let (event_tx, mut event_rx) = broadcast::channel(32);
        let (response_tx, _) = broadcast::channel(32);
        let user_input = UserInput::new(Arc::new(RwLock::new(Transport::new(
            event_tx,
            response_tx.clone(),
        ))));

        // Spawn response handler
        let handle = tokio::spawn(async move {
            let mut received = 0;
            while let Ok(request) = event_rx.recv().await {
                response_tx
                    .send(
                        serde_json::to_value(UserInputResponse {
                            request_id: request["request_id"].as_str().unwrap().to_string(),
                            answer: format!("Concurrent answer {}", received + 1),
                        })
                        .unwrap(),
                    )
                    .unwrap();

                received += 1;
                if received >= 10 {
                    break;
                }
            }
        });

        // Create multiple concurrent requests
        let mut handles = Vec::new();
        for i in 0..10 {
            let user_input = user_input.clone();
            let handle = tokio::spawn(async move {
                let request = UserInputRequest {
                    question: format!("Concurrent question {}", i),
                    context: None,
                    request_id: Uuid::new_v4().to_string(),
                };
                user_input.call(request).await
            });
            handles.push(handle);
        }

        // Wait for all requests to complete and verify responses
        for (i, handle) in handles.into_iter().enumerate() {
            let result = handle.await.unwrap().unwrap();
            assert_eq!(result.answer, format!("Concurrent answer {}", i + 1));
        }

        handle.await.unwrap();
    }
}
