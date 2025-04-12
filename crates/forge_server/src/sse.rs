use std::convert::Infallible;

use axum::response::sse::Event;
use forge_domain::{AgentMessage, ChatResponse};
use forge_stream::MpscStream;
use futures::stream::{Stream, StreamExt};

/// Convert a stream of agent messages to SSE events
pub fn message_stream_to_sse(
    stream: MpscStream<anyhow::Result<AgentMessage<ChatResponse>, anyhow::Error>>,
) -> impl Stream<Item = std::result::Result<Event, Infallible>> {
    stream.map(|result| {
        let event = match result {
            Ok(agent_message) => {
                // Manually create a JSON representation since AgentMessage might not implement
                // Serialize
                let message_type = match &agent_message.message {
                    ChatResponse::Text(_) => "text",
                    ChatResponse::ToolCallStart(_) => "toolCallStart",
                    ChatResponse::ToolCallEnd(_) => "toolCallEnd",
                    ChatResponse::Usage(_) => "usage",
                    ChatResponse::Event(_) => "event",
                };

                // Create a simplified JSON representation
                let json = format!(
                    r#"{{"agent":"{}", "type":"{}", "data":{}}}"#,
                    agent_message.agent,
                    message_type,
                    serde_json::to_string(&agent_message.message)
                        .unwrap_or_else(|_| "null".to_string())
                );

                Event::default().data(json).event("message")
            }
            Err(error) => {
                let error_json = format!(r#"{{ "error": "{}" }}"#, error);
                Event::default().data(error_json).event("error")
            }
        };

        Ok::<_, Infallible>(event)
    })
}
