use std::sync::Arc;

use anyhow::{Context, Result};
use chrono::{DateTime, NaiveDateTime, Utc};
use diesel::prelude::*;
use diesel::sql_types::{Bool, Text, Timestamp};
use forge_domain::{Snapshot, SnapshotId, SnapshotMeta, SnapshotRepository};

use crate::schema::snapshots;
use crate::sqlite::Sqlite;
use crate::Service;

#[derive(Debug, Insertable, Queryable, QueryableByName)]
#[diesel(table_name = snapshots)]
struct SnapshotEntity {
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
    snapshot_path: String,
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

struct Live {
    pool_service: Arc<dyn Sqlite>,
}

impl Live {
    fn new(pool_service: Arc<dyn Sqlite>) -> Self {
        Self { pool_service }
    }
}

impl Service {
    pub fn snapshot_repo(sql: Arc<dyn Sqlite>) -> impl SnapshotRepository {
        Live::new(sql)
    }
}

#[async_trait::async_trait]
impl SnapshotRepository for Live {
    async fn create_snapshot(&self, file_path: &str, snapshot_path: &str) -> Result<Snapshot> {
        let mut conn = self.pool_service.connection().await.with_context(|| {
            "Failed to acquire database connection for snapshot operation".to_string()
        })?;

        let entity = SnapshotEntity {
            id: SnapshotId::generate().into_string(),
            created_at: Utc::now().naive_utc(),
            updated_at: Utc::now().naive_utc(),
            file_path: file_path.to_string(),
            snapshot_path: snapshot_path.to_string(),
            archived: false,
        };
        diesel::insert_into(snapshots::table)
            .values(&entity)
            .execute(&mut conn)
            .with_context(|| {
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

    async fn restore_snapshot(
        &self,
        file_path: &str,
        snapshot_id: Option<SnapshotId>,
    ) -> Result<()> {
        let mut conn = self.pool_service.connection().await.with_context(|| {
            "Failed to acquire database connection for conversation operation".to_string()
        })?;

        // If Id is present, restore that snapshot and archive after that snapshot else
        // restore the latest snapshot
        if let Some(snapshot_id) = snapshot_id {
            diesel::update(snapshots::table)
                .filter(snapshots::file_path.eq(file_path))
                .filter(snapshots::id.eq(snapshot_id.into_string()))
                .set(snapshots::archived.eq(false))
                .execute(&mut conn)
                .with_context(|| {
                    format!(
                        "Failed to restore snapshot with id: {} - database update failed",
                        snapshot_id
                    )
                })?;
        } else {
            let latest_snapshot = snapshots::table
                .filter(snapshots::file_path.eq(file_path))
                .order(snapshots::created_at.desc())
                .first::<SnapshotEntity>(&mut conn)
                .with_context(|| {
                    format!(
                        "Failed to retrieve latest snapshot for file path: {}",
                        file_path
                    )
                })?;
            diesel::update(snapshots::table)
                .filter(snapshots::file_path.eq(file_path))
                .filter(snapshots::id.eq(&latest_snapshot.id))
                .set(snapshots::archived.eq(false))
                .execute(&mut conn)
                .with_context(|| {
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
        let snapshot = snapshots::table
            .filter(snapshots::id.eq(after.into_string()))
            .first::<SnapshotEntity>(&mut conn)
            .with_context(|| {
                format!(
                    "Failed to retrieve snapshot for archiving with id: {}",
                    after
                )
            })
            .with_context(|| {
                format!(
                    "Failed to archive snapshots created after snapshot with id: {}",
                    after
                )
            })?;

        let _ = diesel::update(snapshots::table)
            .filter(snapshots::file_path.eq(snapshot.file_path))
            .filter(snapshots::created_at.gt(snapshot.created_at))
            .set(snapshots::archived.eq(true))
            .execute(&mut conn)
            .with_context(|| {
                format!(
                    "Failed to archive snapshots created after snapshot with id: {}",
                    after
                )
            })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::sqlite::TestDriver;

    pub struct TestSnapshotStorage;
    impl TestSnapshotStorage {
        pub fn in_memory() -> Result<impl SnapshotRepository> {
            let pool_service = Arc::new(TestDriver::new()?);
            Ok(Live::new(pool_service))
        }
    }

    async fn setup_storage() -> Result<impl SnapshotRepository> {
        TestSnapshotStorage::in_memory()
    }

    async fn create_test_snapshot(
        storage: &impl SnapshotRepository,
        file_path: &str,
    ) -> Result<Snapshot> {
        let snapshot_path = format!("/tmp/test_{}", file_path);
        storage.create_snapshot(file_path, &snapshot_path).await
    }

    #[tokio::test]
    async fn snapshot_can_be_stored_and_retrieved() {
        let storage = setup_storage().await.unwrap();
        let file_path = "test.txt";

        let saved = create_test_snapshot(&storage, file_path).await.unwrap();
        let snapshots = storage.list_snapshots(file_path).await.unwrap();

        assert_eq!(snapshots.len(), 1);
        assert_eq!(saved.file_path, snapshots[0].file_path);
        assert_eq!(saved.snapshot_path, snapshots[0].snapshot_path);
    }

    #[tokio::test]
    async fn list_returns_snapshots_by_file_path() {
        let storage = setup_storage().await.unwrap();

        let snap1 = create_test_snapshot(&storage, "test1.txt").await.unwrap();
        let snap2 = create_test_snapshot(&storage, "test2.txt").await.unwrap();

        let snapshots1 = storage.list_snapshots("test1.txt").await.unwrap();
        let snapshots2 = storage.list_snapshots("test2.txt").await.unwrap();

        assert_eq!(snapshots1.len(), 1);
        assert_eq!(snapshots2.len(), 1);
        assert_eq!(snapshots1[0].id, snap1.id);
        assert_eq!(snapshots2[0].id, snap2.id);
    }

    #[tokio::test]
    async fn archive_marks_later_snapshots_as_archived() {
        let storage = setup_storage().await.unwrap();
        let file_path = "test.txt";

        // Create two snapshots
        let snap1 = create_test_snapshot(&storage, file_path).await.unwrap();
        let snap2 = create_test_snapshot(&storage, file_path).await.unwrap();

        // Archive after first snapshot
        storage.archive_snapshots(snap1.id).await.unwrap();

        let snapshots = storage.list_snapshots(file_path).await.unwrap();
        assert!(
            !snapshots
                .iter()
                .find(|s| s.id == snap1.id)
                .unwrap()
                .archived
        );
        assert!(
            snapshots
                .iter()
                .find(|s| s.id == snap2.id)
                .unwrap()
                .archived
        );
    }

    #[tokio::test]
    async fn restore_latest_snapshot_succeeds() {
        let storage = setup_storage().await.unwrap();
        let file_path = "test.txt";

        let _snap1 = create_test_snapshot(&storage, file_path).await.unwrap();
        let snap2 = create_test_snapshot(&storage, file_path).await.unwrap();

        // Archive all snapshots
        storage.archive_snapshots(snap2.id).await.unwrap();

        // Restore latest
        storage.restore_snapshot(file_path, None).await.unwrap();

        // Verify the latest snapshot is not archived
        let snapshots = storage.list_snapshots(file_path).await.unwrap();
        let latest = snapshots.first().unwrap();
        assert!(!latest.archived);
        assert_eq!(latest.id, snap2.id);
    }

    #[tokio::test]
    async fn restore_specific_snapshot_succeeds() {
        let storage = setup_storage().await.unwrap();
        let file_path = "test.txt";

        let snap = create_test_snapshot(&storage, file_path).await.unwrap();
        storage.archive_snapshots(snap.id).await.unwrap();

        // Restore specific snapshot
        storage
            .restore_snapshot(file_path, Some(snap.id))
            .await
            .unwrap();

        let snapshots = storage.list_snapshots(file_path).await.unwrap();
        assert!(!snapshots[0].archived);
        assert_eq!(snapshots[0].id, snap.id);
    }
}
