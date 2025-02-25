use std::fmt::Display;

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ApiKeyId(Uuid);

impl Display for ApiKeyId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for ApiKeyId {
    fn default() -> Self {
        Self::new()
    }
}

impl ApiKeyId {
    pub fn new() -> Self {
        Self(Uuid::new_v4())
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ApiKey {
    pub id: ApiKeyId,
    pub user_id: String,
    pub key_name: String,
    pub key: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: Option<DateTime<Utc>>,
    pub last_used_at: Option<DateTime<Utc>>,
    pub expires_at: Option<DateTime<Utc>>,
    pub is_deleted: bool,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct NewApiKey {
    pub user_id: String,
    pub key_name: String,
    pub key: String,
}

impl Into<String> for NewApiKey {
    fn into(self) -> String {
        serde_json::to_string(&self).unwrap()
    }
}

impl NewApiKey {
    pub fn new(user_id: String, key_name: String, key: String) -> Self {
        Self { user_id, key_name, key }
    }
}
