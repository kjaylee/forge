use async_trait::async_trait;
use derive_setters::Setters;
use serde::{Deserialize, Serialize};
use derive_more::derive::Display;
use uuid::Uuid;
use crate::{Error, Result};
use chrono::{DateTime, Utc};

#[derive(Debug, Display, Serialize, Deserialize, Clone, PartialEq, Eq, Copy)]
#[serde(transparent)]
pub struct SnapshotId(Uuid);

impl SnapshotId {
    pub fn generate() -> Self {
        Self(Uuid::new_v4())
    }

    pub fn into_string(&self) -> String {
        self.0.to_string()
    }

    pub fn parse(value: impl ToString) -> Result<Self> {
        Ok(Self(
            Uuid::parse_str(&value.to_string()).map_err(Error::SnapshotId)?,
        ))
    }
}

#[derive(Debug, Setters, Serialize, Deserialize)]
pub struct Snapshot {
    pub id: SnapshotId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<SnapshotMeta>,
    pub file_path: String,
    pub snapshot_path: String,
    pub archived: bool,

}

impl Snapshot {
    pub fn new(file_path: String, snapshot_path: String) -> Self {
        Self {
            id: SnapshotId::generate(),
            meta: None,
            file_path,
            snapshot_path,
            archived: false,
        }
    }
    
}

#[derive(Debug, Serialize, Deserialize)]
pub struct SnapshotMeta {
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[async_trait]
pub trait SnapshotRepository: Send + Sync {
    fn create_snapshot(file_path: &str) -> Result<Snapshot>;
    fn list_snapshots(file_path: &str) -> Result<Vec<Snapshot>>;
    fn restore_snapshot(
        file_path: &str,
        snapshot_id: Option<SnapshotId>,
    ) -> Result<()>;
    fn archive_snapshots(before: SnapshotId) -> Result<()> ;
}