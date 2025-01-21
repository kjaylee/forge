use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::BreakPoint;


/// Represents the available transformation types
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum TransformType {
    Remove,
    Summarize {
        model_id: String,
    }
}

/// Configuration for message transformations
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema, PartialEq)]
pub struct TransformConfig {
    pub transform_type: TransformType,
    pub breakpoint: BreakPoint,
}

impl TransformConfig {
    pub fn new(transform_type: TransformType, breakpoint: BreakPoint) -> Self {
        Self {
            transform_type,
            breakpoint,
        }
    }
}