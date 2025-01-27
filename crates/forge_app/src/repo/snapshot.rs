use std::sync::Arc;

use anyhow::{Context, Result};
use chrono::{DateTime, NaiveDateTime, Utc};
use diesel::{prelude::*, sql_types::{Bool, Text, Timestamp}};
use forge_domain::{Snapshot, SnapshotId, SnapshotMeta, SnapshotRepository};
use sha2::{Sha256, Digest};
use crate::{schema::snapshots, sqlite::Sqlite};

#[derive(Debug, Insertable, Queryable, QueryableByName)]
#[diesel(table_name = snapshots)]
struct SnapshotEntity{
    #[diesel(sql_type = Text)]
    id: String,
    #[diesel(sql_type = Timestamp)]
    created_at: NaiveDateTime,
    #[diesel(sql_type = Timestamp)]
    updated_at: NaiveDateTime,
    #[diesel(sql_type = Text)]
    file_path: String,
    #[diesel(sql_type = Bool)]
    archived: bool,
    #[diesel(sql_type = Text)]
    snapshot_path:String,
}

impl TryFrom<SnapshotEntity> for Snapshot {
    type Error = anyhow::Error;

    fn try_from(raw: SnapshotEntity) -> Result<Self, Self::Error> {
        Ok(Snapshot {
            id: {
                let id_str = raw.id.clone();
                SnapshotId::parse(raw.id)
                    .with_context(|| format!("Failed to parse snapshot ID: {}", id_str))?
            },
            meta: Some(SnapshotMeta {
                created_at: DateTime::from_naive_utc_and_offset(raw.created_at, Utc),
                updated_at: DateTime::from_naive_utc_and_offset(raw.updated_at, Utc),
            }),
            file_path: raw.file_path,
            snapshot_path: raw.snapshot_path,
            archived: raw.archived,
        })
    } 
}

pub struct Live {
    pool_service: Arc<dyn Sqlite>,
}

impl Live {
    pub fn new(pool_service: Arc<dyn Sqlite>) -> Self {
        Self { pool_service }
    }
    async fn copy_file_with_hashed_name(file_path: &str) -> Result<String> {
        // Read the file's content
        let content = tokio::fs::read(file_path).await?;
    
        // Create a SHA256 hash combining file path and file content
        let mut hasher = Sha256::new();
        hasher.update(file_path.as_bytes());
        hasher.update(&content);
    
        // Convert the hash to a hexadecimal string
        let hash = format!("{:x}", hasher.finalize());
    
        // Create a path in the system temp directory
        let mut temp_path = std::env::temp_dir();
        temp_path.push(&hash);
    
        // Write the file content to the new temp file
        tokio::fs::write(&temp_path, &content).await?;
    
        // Return the new file path as a string
        Ok(temp_path.to_string_lossy().to_string())
    }
}

#[async_trait::async_trait]
impl SnapshotRepository for Live {
    async fn create_snapshot(&self, file_path: &str) -> Result<Snapshot> {
        let mut conn = self.pool_service.connection().await.with_context(|| {
            "Failed to acquire database connection for conversation operation".to_string()
        })?;
        // create a file in temp directory which will copy the content of the file_path and the name of the file will be the sha256 hash of the file_path and its content

        let snapshot_path = Self::copy_file_with_hashed_name(file_path).await.with_context(|| {
            format!("Failed to create snapshot for file path: {}", file_path)
        })?;
    
        let entity = SnapshotEntity {
            id: SnapshotId::generate().into_string(),
            created_at: Utc::now().naive_utc(),
            updated_at: Utc::now().naive_utc(),
            file_path: file_path.to_string(),
            snapshot_path: snapshot_path,
            archived: false,
        };
        diesel::insert_into(snapshots::table)
            .values(&entity)
            .execute(&mut conn).with_context(|| {
                format!(
                    "Failed to save snapshot with id: {} - database insert failed",
                    entity.id
                )
            })?;

        Ok(Snapshot::try_from(entity)?)
    }

    async fn list_snapshots(&self, file_path: &str) -> Result<Vec<Snapshot>> {
        let mut conn = self.pool_service.connection().await.with_context(|| {
            "Failed to acquire database connection for conversation operation".to_string()
        })?;
        let entities = snapshots::table
            .filter(snapshots::file_path.eq(file_path))
            .order(snapshots::created_at.desc())
            .load::<SnapshotEntity>(&mut conn)?;
        entities.into_iter().map(Snapshot::try_from).collect()
    }

    async fn restore_snapshot(&self, file_path: &str, snapshot_id: Option<SnapshotId>) -> Result<()> {
        let mut conn = self.pool_service.connection().await.with_context(|| {
            "Failed to acquire database connection for conversation operation".to_string()
        })?;
        
        // If Id is present, restore that snapshot and archive after that snapshot else restore the latest snapshot
        if let Some(snapshot_id) = snapshot_id {
            diesel::update(snapshots::table)
                .filter(snapshots::file_path.eq(file_path))
                .filter(snapshots::id.eq(snapshot_id.into_string()))
                .set(snapshots::archived.eq(false))
                .execute(&mut conn).with_context(|| {
                    format!(
                        "Failed to restore snapshot with id: {} - database update failed",
                        snapshot_id
                    )
                })?;
        } else {
            let latest_snapshot = snapshots::table
                .filter(snapshots::file_path.eq(file_path))
                .order(snapshots::created_at.desc())
                .first::<SnapshotEntity>(&mut conn).with_context(|| {
                    format!(
                        "Failed to retrieve latest snapshot for file path: {}",
                        file_path
                    )
                })?;
            diesel::update(snapshots::table)
                .filter(snapshots::file_path.eq(file_path))
                .filter(snapshots::id.eq(&latest_snapshot.id))
                .set(snapshots::archived.eq(false))
                .execute(&mut conn).with_context(|| {
                    format!(
                        "Failed to restore latest snapshot with id: {} - database update failed",
                        latest_snapshot.id
                    )
                })?;
        }
        Ok(())

    }

    async fn archive_snapshots(&self, after: SnapshotId) -> Result<()> {
        let mut conn = self.pool_service.connection().await.with_context(|| {
            "Failed to acquire database connection for conversation operation".to_string()
        })?;
        // We need to archive every snapshot that was created after the snapshot corresponding to the given UUID. Because the snapshot ID is a UUID and cannot be directly compared, we must first locate the exact snapshot with that ID. Then, we gather all subsequent snapshots and proceed to archive them.
        let snapshot = snapshots::table
            .filter(snapshots::id.eq(after.into_string()))
            .first::<SnapshotEntity>(&mut conn).with_context(|| {
                format!(
                    "Failed to retrieve snapshot for archiving with id: {}",
                    after
                )
            }).with_context(|| {
                format!(
                    "Failed to archive snapshots created after snapshot with id: {}",
                    after
                )
            })?;

            let _ = diesel::update(snapshots::table)
                .filter(snapshots::file_path.eq(snapshot.file_path))
                .filter(snapshots::created_at.gt(snapshot.created_at))
                .set(snapshots::archived.eq(true))
                .execute(&mut conn).with_context(|| {
                    format!(
                        "Failed to archive snapshots created after snapshot with id: {}",
                        after
                    )
                })?;
        Ok(())
    }
    
}