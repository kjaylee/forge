use derive_setters::Setters;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct KnowledgeId(u64);

impl KnowledgeId {
    pub fn new(id: u64) -> Self {
        Self(id)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Knowledge {
    pub id: KnowledgeId,
    pub content: String,
    pub embedding: Vec<f32>,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Setters)]
#[setters(strip_option, into)]
pub struct Query {
    pub input: String,
    pub limit: Option<usize>,
    pub distance: Option<f32>,
}

impl Query {
    pub fn new(input: String) -> Self {
        Self { input, limit: None, distance: None }
    }
}
