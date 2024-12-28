use derive_more::derive::From;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};

use crate::Result;

#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct System;

#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct User;

#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize)]
pub struct Assistant;

pub trait Role {
    fn name() -> String;
}

impl Role for System {
    fn name() -> String {
        "system".to_string()
    }
}

impl Role for User {
    fn name() -> String {
        "user".to_string()
    }
}

impl Role for Assistant {
    fn name() -> String {
        "assistant".to_string()
    }
}

#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize, Setters)]
pub struct Message<R: Role> {
    pub content: String,
    #[serde(skip)]
    _r: std::marker::PhantomData<R>,
}

impl<T: Role> Message<T> {
    pub fn extend(self, other: Message<T>) -> Message<T> {
        Message {
            content: format!("{}\n{}", self.content, other.content),
            _r: Default::default(),
        }
    }
}

impl Message<System> {
    pub fn system(content: impl Into<String>) -> Self {
        Message { content: content.into(), _r: Default::default() }
    }
}

impl Message<User> {
    pub fn user(content: impl Into<String>) -> Self {
        Message { content: content.into(), _r: Default::default() }
    }

    /// Creates a user message from any serializable item. The message is
    /// typically in a XML format
    pub fn try_from(item: impl Serialize) -> Result<Self> {
        Ok(Message::user(serde_json::to_string(&item)?))
    }
}

impl Message<Assistant> {
    pub fn assistant(content: impl Into<String>) -> Self {
        Message { content: content.into(), _r: Default::default() }
    }
}

#[derive(Clone, Debug, Deserialize, From, PartialEq, Serialize)]
pub enum AnyMessage {
    System(Message<System>),
    User(Message<User>),
    Assistant(Message<Assistant>),
}

impl AnyMessage {
    pub fn content(&self) -> &str {
        match self {
            AnyMessage::System(msg) => msg.content.as_str(),
            AnyMessage::User(msg) => msg.content.as_str(),
            AnyMessage::Assistant(msg) => msg.content.as_str(),
        }
    }

    pub fn role(&self) -> String {
        match self {
            AnyMessage::System(_) => System::name(),
            AnyMessage::User(_) => User::name(),
            AnyMessage::Assistant(_) => Assistant::name(),
        }
    }
}
