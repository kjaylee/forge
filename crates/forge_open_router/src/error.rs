use std::collections::HashMap;

use derive_more::derive::Display;
use thiserror::Error;

#[derive(Debug, Display, derive_more::From, Error)]
pub enum Error {
    EmptyContent,
    #[from(ignore)]
    #[display("Upstream: message: {},{}", message, match metadata.is_empty() {
        true => String::new(),
        false => format!("details: {:?}", metadata)
    })]
    Upstream {
        code: u32,
        message: String,
        metadata: HashMap<String, serde_json::Value>,
    },
    SerdeJson(serde_json::Error),
    ToolCallMissingName,
}
