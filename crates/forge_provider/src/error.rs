use std::sync::Arc;

use derive_more::derive::Display;
use forge_domain::ModelId;
use thiserror::Error;

#[derive(Debug, Display, derive_more::From, Error)]
pub enum Error {
    // Custom display message for provider error
    EmptyContent,
    ModelNotFound(ModelId),
    #[from(ignore)]
    #[display("Upstream: {}", 1)]
    Upstream {
        code: u32,
        message: String,
    },
    Reqwest(reqwest::Error),
    SerdeJson(serde_json::Error),
    EventSource(reqwest_eventsource::Error),
    ToolCallMissingName,
    Arc(Arc<Error>),
}

pub type Result<T> = std::result::Result<T, Error>;
