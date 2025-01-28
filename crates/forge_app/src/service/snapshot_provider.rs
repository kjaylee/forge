use std::sync::Arc;

use anyhow::{Context, Result};
use async_trait::async_trait;
use forge_domain::{Snapshot, SnapshotId, SnapshotProvider as SnapshotProviderTrait, SnapshotRepository};
use sha2::{Digest, Sha256};

/// Provides file-system level snapshot operations while coordinating with the SnapshotRepository
/// for persistent storage
pub struct SnapshotProvider {
    repository: Arc<dyn SnapshotRepository>,
}

impl SnapshotProvider {
    pub fn new(repository: Arc<dyn SnapshotRepository>) -> Self {
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

#[async_trait]
impl SnapshotProviderTrait for SnapshotProvider {
    async fn create_snapshot(&self, file_path: &str) -> Result<Snapshot> {
        let (snapshot_path, exists) = Self::copy_file_with_hashed_name(file_path)
            .await
            .with_context(|| format!("Failed to create snapshot for file path: {}", file_path))?;

        if exists {
            // If snapshot exists, find it in the repository
            let snapshots = self.repository.list_snapshots(file_path).await?;
            if let Some(snapshot) = snapshots.into_iter().find(|s| s.snapshot_path == snapshot_path) {
                return Ok(snapshot);
            }
        }

        // If we get here, either the file is new or it wasn't in the database
        self.repository.create_snapshot(file_path, &snapshot_path).await
    }

    async fn list_snapshots(&self, file_path: &str) -> Result<Vec<Snapshot>> {
        self.repository.list_snapshots(file_path).await
    }

    async fn restore_snapshot(&self, file_path: &str, snapshot_id: Option<SnapshotId>) -> Result<()> {
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
            .with_context(|| format!("Failed to read snapshot content from: {}", snapshot.snapshot_path))?;

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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use tokio::sync::Mutex;
    use super::*;

    /// A test implementation of the SnapshotProvider trait for use in tests
    pub struct TestSnapshotProvider {
        /// Maps file paths to their snapshot content
        snapshots: Arc<Mutex<HashMap<String, Vec<u8>>>>,
    }

    impl TestSnapshotProvider {
        pub fn new() -> Self {
            Self {
                snapshots: Arc::new(Mutex::new(HashMap::new())),
            }
        }

        pub async fn get_snapshot_content(&self, file_path: &str) -> Option<Vec<u8>> {
            let snapshots = self.snapshots.lock().await;
            snapshots.get(file_path).cloned()
        }
    }

    impl Default for TestSnapshotProvider {
        fn default() -> Self {
            Self::new()
        }
    }

    #[async_trait]
    impl SnapshotProviderTrait for TestSnapshotProvider {
        async fn create_snapshot(&self, file_path: &str) -> Result<Snapshot> {
            // For testing, we'll just store the file path as content
            let mut snapshots = self.snapshots.lock().await;
            snapshots.insert(file_path.to_string(), file_path.as_bytes().to_vec());

            Ok(Snapshot::new(
                file_path.to_string(),
                format!("/tmp/test_snapshot_{}", file_path),
            ))
        }

        async fn list_snapshots(&self, file_path: &str) -> Result<Vec<Snapshot>> {
            let snapshots = self.snapshots.lock().await;
            Ok(if snapshots.contains_key(file_path) {
                vec![Snapshot::new(
                    file_path.to_string(),
                    format!("/tmp/test_snapshot_{}", file_path),
                )]
            } else {
                vec![]
            })
        }

        async fn restore_snapshot(&self, file_path: &str, _snapshot_id: Option<SnapshotId>) -> Result<()> {
            // For testing, we don't need to actually restore files
            let snapshots = self.snapshots.lock().await;
            if !snapshots.contains_key(file_path) {
                anyhow::bail!("No snapshot found for file: {}", file_path);
            }
            Ok(())
        }

        async fn archive_snapshots(&self, _after: SnapshotId) -> Result<()> {
            // For testing, we don't need to actually archive snapshots
            Ok(())
        }
    }

    // Add actual tests for both implementations
    #[tokio::test]
    async fn test_snapshot_provider_create_and_list() -> Result<()> {
        let provider = TestSnapshotProvider::default();
        let file_path = "test.txt";
        
        // Create a snapshot
        let snapshot = provider.create_snapshot(file_path).await?;
        assert_eq!(snapshot.file_path, file_path);

        // List snapshots
        let snapshots = provider.list_snapshots(file_path).await?;
        assert_eq!(snapshots.len(), 1);
        assert_eq!(snapshots[0].file_path, file_path);

        Ok(())
    }

    #[tokio::test]
    async fn test_snapshot_provider_restore() -> Result<()> {
        let provider = TestSnapshotProvider::default();
        let file_path = "test.txt";

        // Try to restore without creating - should fail
        assert!(provider.restore_snapshot(file_path, None).await.is_err());

        // Create a snapshot
        let snapshot = provider.create_snapshot(file_path).await?;

        // Restore should now succeed
        assert!(provider.restore_snapshot(file_path, Some(snapshot.id)).await.is_ok());

        Ok(())
    }

    use std::sync::Arc;
    use tempfile::NamedTempFile;
    use tokio::fs::File;
    use tokio::io::AsyncWriteExt;

    // Helper function to create a test file with content
    async fn create_test_file(content: &str) -> Result<(String, NamedTempFile)> {
        let file = NamedTempFile::new()?;
        let path = file.path().to_string_lossy().to_string();
        let mut file_handle = File::create(&path).await?;
        file_handle.write_all(content.as_bytes()).await?;
        Ok((path, file))
    }

    // Mock repository for testing
    #[derive(Default)]
    struct MockSnapshotRepository {
        snapshots: Arc<Mutex<Vec<Snapshot>>>,
    }

    #[async_trait]
    impl SnapshotRepository for MockSnapshotRepository {
        async fn create_snapshot(&self, file_path: &str, snapshot_path: &str) -> Result<Snapshot> {
            let mut snapshots = self.snapshots.lock().await;
            let snapshot = Snapshot::new(file_path.to_string(), snapshot_path.to_string());
            snapshots.push(snapshot.clone());
            Ok(snapshot)
        }

        async fn list_snapshots(&self, file_path: &str) -> Result<Vec<Snapshot>> {
            let snapshots = self.snapshots.lock().await;
            Ok(snapshots.iter().filter(|s| s.file_path == file_path).cloned().collect())
        }

        async fn restore_snapshot(&self, _file_path: &str, _snapshot_id: Option<SnapshotId>) -> Result<()> {
            Ok(())
        }

        async fn archive_snapshots(&self, _after: SnapshotId) -> Result<()> {
            Ok(())
        }
    }

    #[tokio::test]
    async fn test_snapshot_deduplication() -> Result<()> {
        // Create a test file
        let (file_path, _file) = create_test_file("test content").await?;

        // Create provider with mock repository
        let repo = Arc::new(MockSnapshotRepository::default());
        let provider = SnapshotProvider::new(repo.clone());

        // Create first snapshot
        let snapshot1 = provider.create_snapshot(&file_path).await?;
        
        // Create second snapshot of the same file
        let snapshot2 = provider.create_snapshot(&file_path).await?;

        // Should return the same snapshot
        assert_eq!(snapshot1.snapshot_path, snapshot2.snapshot_path);

        // Check that only one snapshot was stored in the repository
        let snapshots = repo.list_snapshots(&file_path).await?;
        assert_eq!(snapshots.len(), 1);

        Ok(())
    }

    #[tokio::test]
    async fn test_snapshot_different_content() -> Result<()> {
        // Create two test files with different content
        let (file_path1, _file1) = create_test_file("test content 1").await?;
        let (file_path2, _file2) = create_test_file("test content 2").await?;

        // Create provider with mock repository
        let repo = Arc::new(MockSnapshotRepository::default());
        let provider = SnapshotProvider::new(repo.clone());

        // Create snapshots
        let snapshot1 = provider.create_snapshot(&file_path1).await?;
        let snapshot2 = provider.create_snapshot(&file_path2).await?;

        // Should have different snapshot paths
        assert_ne!(snapshot1.snapshot_path, snapshot2.snapshot_path);

        // Check that both snapshots were stored
        let all_snapshots = vec![repo.list_snapshots(&file_path1).await?, 
                                repo.list_snapshots(&file_path2).await?]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(all_snapshots.len(), 2);

        Ok(())
    }
}