use std::pin::Pin;

use std::fmt;
use serde_json::Value;

#[derive(Debug)]
pub enum Error {
    Provider {
        provider: String,
        error: ProviderError,
    },
    Reqwest(reqwest::Error),
    SerdeJson(serde_json::Error),
    EventSource(reqwest_eventsource::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Provider { error, .. } => write!(f, "{}", error),
            Error::Reqwest(e) => write!(f, "{}", e),
            Error::SerdeJson(e) => write!(f, "{}", e),
            Error::EventSource(e) => write!(f, "{}", e),
        }
    }
}

impl From<reqwest::Error> for Error {
    fn from(err: reqwest::Error) -> Self {
        Error::Reqwest(err)
    }
}

impl From<serde_json::Error> for Error {
    fn from(err: serde_json::Error) -> Self {
        Error::SerdeJson(err)
    }
}

impl From<reqwest_eventsource::Error> for Error {
    fn from(err: reqwest_eventsource::Error) -> Self {
        Error::EventSource(err)
    }
}

impl Error {
    pub fn empty_response(provider: impl Into<String>) -> Self {
        Error::Provider {
            provider: provider.into(),
            error: ProviderError::EmptyContent,
        }
    }
}

#[derive(Debug)]
pub enum ProviderError {
    EmptyContent,
    ToolUseEmptyName,
    UpstreamError(Value),
    AuthenticationError,
}

impl fmt::Display for ProviderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProviderError::EmptyContent => write!(f, "Empty response from provider"),
            ProviderError::ToolUseEmptyName => write!(f, "Tool use missing name"),
            ProviderError::UpstreamError(v) => write!(f, "Upstream error: {}", v),
            ProviderError::AuthenticationError => write!(f, "Authentication failed - please check your API key"),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;
pub type BoxStream<A, E> =
    Pin<Box<dyn tokio_stream::Stream<Item = std::result::Result<A, E>> + Send>>;
pub type ResultStream<A, E> = std::result::Result<BoxStream<A, E>, E>;
