use axum::response::sse::Event;
use forge_domain::{AgentMessage, ChatResponse};
use forge_stream::MpscStream;
use futures::stream::{Stream, StreamExt};

use crate::Result;

/// Convert a stream of agent messages to SSE events
pub fn message_stream_to_sse(
    stream: MpscStream<anyhow::Result<AgentMessage<ChatResponse>>>,
) -> impl Stream<Item = Result<Event>> {
    stream.map(|message| match message {
        Ok(message) => into_event(message),
        Err(error) => Err(error.into()),
    })
}

fn into_event(message: AgentMessage<ChatResponse>) -> Result<Event> {
    let message = serde_json::to_string(&message)?;
    Ok(Event::default().data(message))
}
