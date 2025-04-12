use std::convert::Infallible;

use axum::response::sse::Event;
use forge_domain::{AgentMessage, ChatResponse, MessageType, SseError, SseEventType, SseMessage};
use forge_stream::MpscStream;
use futures::stream::{Stream, StreamExt};

/// Convert a stream of agent messages to SSE events
pub fn message_stream_to_sse(
    stream: MpscStream<anyhow::Result<AgentMessage<ChatResponse>, anyhow::Error>>,
) -> impl Stream<Item = std::result::Result<Event, Infallible>> {
    stream.map(|result| {
        let event = match result {
            Ok(agent_message) => {
                // Determine message type based on ChatResponse variant
                let message_type = match &agent_message.message {
                    ChatResponse::Text { .. } => MessageType::Text,
                    ChatResponse::ToolCallStart(_) => MessageType::ToolCallStart,
                    ChatResponse::ToolCallEnd(_) => MessageType::ToolCallEnd,
                    ChatResponse::Usage(_) => MessageType::Usage,
                    ChatResponse::Event(_) => MessageType::Event,
                };

                // Create a structured message
                let sse_message = SseMessage {
                    agent: agent_message.agent.as_str().to_string(),
                    message_type,
                    data: serde_json::to_value(&agent_message.message)
                        .unwrap_or(serde_json::Value::Null),
                };

                // Serialize the structured message
                let json = serde_json::to_string(&sse_message)
                    .unwrap_or_else(|_| r#"{"error":"Failed to serialize message"}"#.to_string());

                Event::default()
                    .data(json)
                    .event(SseEventType::Message.to_string())
            }
            Err(error) => {
                // Create a structured error
                let sse_error = SseError { error: error.to_string() };

                // Serialize the structured error
                let error_json = serde_json::to_string(&sse_error)
                    .unwrap_or_else(|_| r#"{"error":"Failed to serialize error"}"#.to_string());

                Event::default()
                    .data(error_json)
                    .event(SseEventType::Error.to_string())
            }
        };

        Ok::<_, Infallible>(event)
    })
}
