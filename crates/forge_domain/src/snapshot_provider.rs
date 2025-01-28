use anyhow::Result;
use async_trait::async_trait;

use crate::{Snapshot, SnapshotId};

/// Provides high-level snapshot operations including file management
#[async_trait]
pub trait SnapshotProvider: Send + Sync {
    /// Creates a new snapshot of the file at the given path.
    /// This includes:
    /// 1. Creating a copy of the file in a temporary location
    /// 2. Storing the snapshot metadata in the repository
    async fn create_snapshot(&self, file_path: &str) -> Result<Snapshot>;

    /// Lists all snapshots for a given file path
    async fn list_snapshots(&self, file_path: &str) -> Result<Vec<Snapshot>>;

    /// Restores a file to a specific snapshot state
    /// If no snapshot_id is provided, restores to the latest snapshot
    async fn restore_snapshot(
        &self,
        file_path: &str,
        snapshot_id: Option<SnapshotId>,
    ) -> Result<()>;

    /// Archives all snapshots created after the specified snapshot
    async fn archive_snapshots(&self, after: SnapshotId) -> Result<()>;
}
