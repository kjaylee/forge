use derive_more::derive::Display;
use thiserror::Error;

use crate::response::ErrorResponse;

#[derive(Debug, Display, derive_more::From, Error)]
pub enum Error {
    EmptyContent,
    Upstream(ErrorResponse),
    SerdeJson(serde_json::Error),
    ToolCallMissingName,
}
