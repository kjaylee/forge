use std::fmt;

use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LearningId(pub Uuid);

impl Default for LearningId {
    fn default() -> Self {
        Self::new()
    }
}

impl LearningId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }

    pub fn from_uuid(uuid: Uuid) -> Self {
        Self(uuid)
    }

    pub fn as_uuid(&self) -> &Uuid {
        &self.0
    }
}

impl fmt::Display for LearningId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Knowledge {
    pub id: LearningId,
    pub content: String,
    pub embedding: Vec<f32>,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Default, Debug, Clone, Setters)]
#[setters(strip_option, into)]
pub struct Query {
    pub input: Option<String>,
    pub limit: Option<usize>,
    pub distance: Option<f32>,
}
