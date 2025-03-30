use std::pin::Pin;

use thiserror::Error;

use crate::{AgentId, ConversationId};

// NOTE: Deriving From for error is a really bad idea. This is because you end
// up converting errors incorrectly without much context. For eg: You don't want
// all serde error to be treated as the same. Instead we want to know exactly
// where that serde failure happened and for what kind of value.
#[derive(Debug, Error)]
pub enum Error {
    #[error("Missing tool name")]
    ToolCallMissingName,

    #[error("Invalid tool call arguments: {0}")]
    ToolCallArgument(serde_json::Error),

    #[error("Invalid tool call XML: {0}")]
    ToolCallParse(String),

    #[error("Invalid conversation id: {0}")]
    ConversationId(uuid::Error),

    #[error("Agent not found in the arena: {0}")]
    AgentUndefined(AgentId),

    #[error("Variable not found in output: {0}")]
    UndefinedVariable(String),

    #[error("Head agent not found")]
    HeadAgentUndefined,

    #[error("Agent '{0}' has reached max turns of {1}")]
    MaxTurnsReached(AgentId, u64),

    #[error("Conversation not found: {0}")]
    ConversationNotFound(ConversationId),

    #[error("Missing description for agent: {0}")]
    MissingAgentDescription(AgentId),
    #[error("Missing model for agent: {0}")]
    MissingModel(AgentId),
}

/// Serializable error type for use in retry events
#[derive(Debug, Clone, serde::Serialize)]
pub struct RetryError {
    /// Error message
    pub message: String,
    /// Error kind/type - only set for known retriable errors
    pub kind: Option<RetryErrorKind>,
}

/// Kinds of errors that can be retried
#[derive(Debug, Clone, serde::Serialize)]
pub enum RetryErrorKind {
    /// Missing tool name
    ToolCallMissingName,
    /// Invalid tool call arguments
    ToolCallArgument,
    /// Invalid tool call XML
    ToolCallParse,
}

impl RetryError {
    /// Create a new retry error from an anyhow error
    pub fn from_error(err: &anyhow::Error) -> Self {
        if let Some(domain_err) = err.downcast_ref::<Error>() {
            // Only set kind for specific retriable errors
            let kind = match domain_err {
                Error::ToolCallMissingName => Some(RetryErrorKind::ToolCallMissingName),
                Error::ToolCallArgument(_) => Some(RetryErrorKind::ToolCallArgument),
                Error::ToolCallParse(_) => Some(RetryErrorKind::ToolCallParse),
                _ => None,
            };

            Self { message: format!("{}", err), kind }
        } else {
            // For non-domain errors, don't specify a kind
            Self { message: format!("{}", err), kind: None }
        }
    }

    /// Check if an error is retriable
    pub fn is_retriable(err: &anyhow::Error) -> bool {
        if let Some(domain_err) = err.downcast_ref::<Error>() {
            matches!(
                domain_err,
                Error::ToolCallParse(_) | Error::ToolCallArgument(_) | Error::ToolCallMissingName
            )
        } else {
            false
        }
    }
}

pub type Result<A> = std::result::Result<A, Error>;
pub type BoxStream<A, E> =
    Pin<Box<dyn tokio_stream::Stream<Item = std::result::Result<A, E>> + Send>>;

pub type ResultStream<A, E> = std::result::Result<BoxStream<A, E>, E>;
