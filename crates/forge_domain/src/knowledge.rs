use chrono::Utc;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct KnowledgeId(Uuid);

impl KnowledgeId {
    pub fn generate() -> Self {
        Self(Uuid::new_v4())
    }

    pub fn into_uuid(self) -> Uuid {
        self.0
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Knowledge<C> {
    pub id: KnowledgeId,
    pub content: C,
    pub embedding: Vec<f32>,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

impl<C> Knowledge<C> {
    /// Embedding can be created from a part or more of the actual content.
    pub fn new(content: C, embedding: Vec<f32>) -> Self {
        let now = Utc::now();
        Self {
            id: KnowledgeId::generate(),
            content,
            embedding,
            created_at: now,
            updated_at: now,
        }
    }
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
