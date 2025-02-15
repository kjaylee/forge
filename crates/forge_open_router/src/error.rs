use reqwest_eventsource::CannotCloneRequestError;
use thiserror::Error;
use url::{ParseError, Url};

use crate::response::ErrorResponse;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Empty Response")]
    EmptyContent,
    #[error("Upstream: {_0}")]
    Upstream(ErrorResponse),
    #[error("Tool call missing name")]
    ToolCallMissingName,
    #[error("Invalid path: Contains forbidden patterns in {_0}")]
    InvalidURLPath(String),
    #[error("Failed to create a valid URL from base_url {_1} and path {_2}: {_0}")]
    InvalidURL(ParseError, Url, String),
    #[error("Request with a streaming body cannot be cloned: {_0}")]
    UncloneableRequestError(CannotCloneRequestError),
    #[error("EventSource stream error: {_0}")]
    EventSourceStreamError(reqwest_eventsource::Error),
    #[error("Failed to parse arguments in ToolCall: {_0}")]
    ToolCallParseError(serde_json::Error),
    #[error("Failed to parse open router response: {_0}")]
    OpenRouterResponseParseError(serde_json::Error),
}

pub type Result<T> = std::result::Result<T, Error>;
