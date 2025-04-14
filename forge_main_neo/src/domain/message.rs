use crossterm::event::Event;
use derive_more::From;
use forge_api::ChatResponse;

#[derive(From)]
pub enum Message {
    Chat(ChatResponse),
    KeyBoard(Event),
}
