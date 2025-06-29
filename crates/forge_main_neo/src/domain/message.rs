/// Enum to differentiate between user and assistant messages
#[derive(Debug, Clone, PartialEq)]
pub enum Message {
    User(String),
    Assistant(String),
}
