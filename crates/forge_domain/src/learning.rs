use std::fmt;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::Error;

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

    pub fn parse(value: impl ToString) -> Result<Self, Error> {
        Ok(Self(Uuid::parse_str(&value.to_string())?))
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
pub struct Learning {
    pub id: LearningId,
    pub current_working_directory: String,
    pub learnings: Vec<String>,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

impl Learning {
    pub fn new(current_working_directory: String, learnings: Vec<String>) -> Self {
        Self {
            id: LearningId::new(),
            current_working_directory,
            learnings,
            created_at: chrono::Utc::now(),
        }
    }
}

#[async_trait]
pub trait LearningRepository: Send + Sync {
    /// List all learning entries
    async fn list_learnings(&self) -> anyhow::Result<Vec<Learning>>;

    /// Get 'N' recent learning of conversations.
    async fn recent_learnings(&self, n: usize) -> anyhow::Result<Vec<Learning>>;

    /// Save Learnings from the conversation
    async fn save(&self, learning: Learning) -> anyhow::Result<()>;
}
