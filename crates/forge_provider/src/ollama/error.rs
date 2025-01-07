use derive_more::Display;
use serde::Deserialize;

#[derive(Debug, Display, derive_more::From)]
pub enum Error {
    // Ollama-specific errors
    #[display("Invalid model configuration")]
    InvalidModel,
    #[display("Ollama connection error")]
    ConnectionError,
    #[display("Invalid response format")]
    InvalidResponse,
    #[display("Stream error: {_0}")]
    StreamError(String),
    // Re-exported errors from common types
    #[from]
    Request(reqwest::Error),
    #[from]
    Json(serde_json::Error),
    #[from]
    Common(crate::error::Error),
    #[from]
    EventSource(reqwest_eventsource::Error),
    EventSourceBuild(reqwest_eventsource::CannotCloneRequestError),
}

#[derive(Debug, Deserialize)]
pub struct OllamaError {
    pub error: String,
}

impl From<OllamaError> for Error {
    fn from(err: OllamaError) -> Self {
        Error::StreamError(err.error)
    }
}

impl From<reqwest_eventsource::CannotCloneRequestError> for Error {
    fn from(err: reqwest_eventsource::CannotCloneRequestError) -> Self {
        Error::EventSourceBuild(err)
    }
}

pub type Result<T> = std::result::Result<T, Error>;
