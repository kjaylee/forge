use std::sync::Arc;

use anyhow::{Context, Result};
use async_trait::async_trait;
use forge_domain::{Snapshot, SnapshotId, SnapshotProvider, SnapshotRepository};
use sha2::{Digest, Sha256};

use super::Service;

/// Provides file-system level snapshot operations while coordinating with the
/// SnapshotRepository for persistent storage
pub struct Live {
    repository: Arc<dyn SnapshotRepository>,
}

impl Live {
    fn new(repository: Arc<dyn SnapshotRepository>) -> Self {
        Self { repository }
    }

    async fn create_hashed_name(file_path: &str) -> Result<(String, bool)> {
        // Read the file's content
        let content = tokio::fs::read(file_path).await?;

        // Create a SHA256 hash combining file path and file content
        let mut hasher = Sha256::new();
        hasher.update(file_path.as_bytes());
        hasher.update(&content);

        // Convert the hash to a hexadecimal string
        let hash = format!("{:x}", hasher.finalize());

        // Check if a file with this hash already exists in temp directory
        let mut temp_path = std::env::temp_dir();
        temp_path.push(&hash);

        let exists = tokio::fs::metadata(&temp_path).await.is_ok();

        Ok((hash, exists))
    }

    async fn get_snapshot_path(hash: &str) -> String {
        let mut temp_path = std::env::temp_dir();
        temp_path.push(hash);
        temp_path.to_string_lossy().to_string()
    }

    async fn copy_file_with_hashed_name(file_path: &str) -> Result<(String, bool)> {
        // Get the hash and check if file exists
        let (hash, exists) = Self::create_hashed_name(file_path).await?;

        if !exists {
            // Read the file's content
            let content = tokio::fs::read(file_path).await?;

            // Create a path in the system temp directory
            let mut temp_path = std::env::temp_dir();
            temp_path.push(&hash);

            // Write the file content to the new temp file
            tokio::fs::write(&temp_path, &content).await?
        }

        Ok((Self::get_snapshot_path(&hash).await, exists))
    }
}

impl Service {
    pub fn snapshot_provider(repository: Arc<dyn SnapshotRepository>) -> impl SnapshotProvider {
        Live::new(repository)
    }
}

#[async_trait]
impl SnapshotProvider for Live {
    async fn create_snapshot(&self, file_path: &str) -> Result<Snapshot> {
        let (snapshot_path, exists) = Self::copy_file_with_hashed_name(file_path)
            .await
            .with_context(|| format!("Failed to create snapshot for file path: {}", file_path))?;

        if exists {
            // If snapshot exists, find it in the repository
            let snapshots = self.repository.list_snapshots(file_path).await?;
            if let Some(snapshot) = snapshots
                .into_iter()
                .find(|s| s.snapshot_path == snapshot_path)
            {
                return Ok(snapshot);
            }
        }

        // If we get here, either the file is new or it wasn't in the database
        self.repository
            .create_snapshot(file_path, &snapshot_path)
            .await
    }

    async fn list_snapshots(&self, file_path: &str) -> Result<Vec<Snapshot>> {
        self.repository.list_snapshots(file_path).await
    }

    async fn restore_snapshot(
        &self,
        file_path: &str,
        snapshot_id: Option<SnapshotId>,
    ) -> Result<()> {
        // First find the snapshot in the repository
        let snapshot = match snapshot_id {
            Some(id) => {
                // Retrieve the specific snapshot by ID
                let snapshots = self.repository.list_snapshots(file_path).await?;
                snapshots
                    .into_iter()
                    .find(|s| s.id == id)
                    .ok_or_else(|| anyhow::anyhow!("Snapshot not found for ID: {}", id))?
            }
            None => {
                // Get the latest snapshot
                let snapshots = self.repository.list_snapshots(file_path).await?;
                snapshots
                    .into_iter()
                    .next()
                    .ok_or_else(|| anyhow::anyhow!("No snapshots found for file: {}", file_path))?
            }
        };

        // Read the snapshot content
        let snapshot_content = tokio::fs::read(&snapshot.snapshot_path)
            .await
            .with_context(|| {
                format!(
                    "Failed to read snapshot content from: {}",
                    snapshot.snapshot_path
                )
            })?;

        // Write the content back to the original file
        tokio::fs::write(file_path, snapshot_content)
            .await
            .with_context(|| format!("Failed to write snapshot content to: {}", file_path))?;

        // Update the repository to mark the snapshot as not archived
        self.repository
            .restore_snapshot(file_path, Some(snapshot.id))
            .await
    }

    async fn archive_snapshots(&self, after: SnapshotId) -> Result<()> {
        self.repository.archive_snapshots(after).await
    }
}
