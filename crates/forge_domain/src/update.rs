use merge::Merge;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UpdateFrequency {
    Daily,
    Weekly,
    Always,
}

#[derive(Debug, Clone, Serialize, Deserialize, Merge, Default)]
pub struct Update {
    pub check_frequency: Option<UpdateFrequency>,
    pub auto_update: Option<bool>,
}
