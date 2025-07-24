use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use crate::ToolName;

#[derive(Clone, Debug, Default, Deserialize, PartialEq, Serialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ToolChoice {
    #[default]
    None,
    Auto,
    Required,
    Call(ToolName),
}

