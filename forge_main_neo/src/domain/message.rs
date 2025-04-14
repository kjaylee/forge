use crossterm::event::Event;
use derive_more::From;
use forge_api::{AgentMessage, ChatResponse};

#[derive(From)]
pub enum Message {
    Chat(AgentMessage<ChatResponse>),
    Initialize,
    KeyBoard(Event),
}
