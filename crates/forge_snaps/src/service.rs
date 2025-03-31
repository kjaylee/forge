use std::path::PathBuf;
use anyhow::Result;
use forge_fs::ForgeFS;
use tokio::fs;

use crate::snapshot::Snapshot;

/// Implementation of the SnapshotService
#[derive(Debug)]
pub struct SnapshotService {
    /// Base directory for storing snapshots
    snapshots_directory: PathBuf,
}

impl SnapshotService {
    /// Create a new FileSystemSnapshotService with a specific home path
    pub fn new(snapshot_base_dir: PathBuf) -> Self {
        Self { snapshots_directory: snapshot_base_dir }
    }
}

impl SnapshotService {
    pub async fn create_snapshot(&self, path: PathBuf) -> Result<Snapshot> {
        let snapshot = Snapshot::create(path).await?;

        // Create intermediary directories if they don't exist
        let snapshot_path = snapshot.snapshot_path(Some(self.snapshots_directory.clone()));
        if let Some(parent) = PathBuf::from(&snapshot_path).parent() {
            ForgeFS::create_dir_all(parent).await?;
        }

        snapshot
            .save(Some(self.snapshots_directory.clone()))
            .await?;

        Ok(snapshot)
    }

    pub async fn undo_snapshot(&self, path: PathBuf) -> Result<()> {
        // Create a temporary snapshot to get the hash directory
        let snapshot = Snapshot::create(path.clone()).await?;
        let hash_dir = self.snapshots_directory.join(snapshot.path_hash());

        // Check if snapshots exist
        if !ForgeFS::exists(&hash_dir) {
            return Err(anyhow::anyhow!("No snapshots found for {:?}", path));
        }

        // List and find the latest snapshot
        let mut entries = fs::read_dir(&hash_dir).await?;
        let mut latest_snapshot = None;
        let mut latest_time = None;

        while let Some(entry) = entries.next_entry().await? {
            let file_name = entry.file_name();
            let file_name = file_name.to_string_lossy();
            
            // Parse the timestamp from the filename (format: YYYY-MM-DD_HH-MM-SS-mmm.snap)
            if let Some(timestamp_str) = file_name.strip_suffix(".snap") {
                if let Ok(timestamp) = chrono::DateTime::parse_from_str(
                    &format!("{} +0000", timestamp_str.replace('_', " ")),
                    "%Y-%m-%d %H-%M-%S-%3f %z",
                ) {
                    if latest_time.is_none() || timestamp > latest_time.unwrap() {
                        latest_time = Some(timestamp);
                        latest_snapshot = Some(entry.path());
                    }
                }
            }
        }

        // Restore the latest snapshot
        if let Some(snapshot_path) = latest_snapshot {
            let content = ForgeFS::read(&snapshot_path).await?;
            ForgeFS::write(&path, content).await?;
            // Remove the snapshot after restoring it
            ForgeFS::remove_file(&snapshot_path).await?;
            Ok(())
        } else {
            Err(anyhow::anyhow!("No valid snapshots found for {:?}", path))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    // Test helpers
    struct TestContext {
        _temp_dir: TempDir,
        _snapshots_dir: PathBuf,
        test_file: PathBuf,
        service: SnapshotService,
    }

    impl TestContext {
        async fn new() -> Result<Self> {
            let temp_dir = TempDir::new()?;
            let snapshots_dir = temp_dir.path().join("snapshots");
            let test_file = temp_dir.path().join("test.txt");
            let service = SnapshotService::new(snapshots_dir.clone());

            Ok(Self {
                _temp_dir: temp_dir,
                _snapshots_dir: snapshots_dir,
                test_file,
                service,
            })
        }

        async fn write_content(&self, content: &str) -> Result<()> {
            ForgeFS::write(&self.test_file, content.as_bytes()).await
        }

        async fn read_content(&self) -> Result<String> {
            let content = ForgeFS::read(&self.test_file).await?;
            Ok(String::from_utf8(content)?)
        }

        async fn create_snapshot(&self) -> Result<Snapshot> {
            self.service.create_snapshot(self.test_file.clone()).await
        }

        async fn undo_snapshot(&self) -> Result<()> {
            self.service.undo_snapshot(self.test_file.clone()).await
        }
    }

    #[tokio::test]
    async fn test_create_snapshot() -> Result<()> {
        // Setup
        let ctx = TestContext::new().await?;
        let test_content = "Hello, World!";
        
        // Test steps
        ctx.write_content(test_content).await?;
        let snapshot = ctx.create_snapshot().await?;
        
        // Verify
        let snapshot_content = ForgeFS::read(&snapshot.path).await?;
        assert_eq!(String::from_utf8(snapshot_content)?, test_content);

        Ok(())
    }

    #[tokio::test]
    async fn test_undo_snapshot() -> Result<()> {
        // Setup
        let ctx = TestContext::new().await?;
        let initial_content = "Initial content";
        let modified_content = "Modified content";
        
        // Test steps
        ctx.write_content(initial_content).await?;
        ctx.create_snapshot().await?;
        ctx.write_content(modified_content).await?;
        ctx.undo_snapshot().await?;
        
        // Verify
        assert_eq!(ctx.read_content().await?, initial_content);

        Ok(())
    }

    #[tokio::test]
    async fn test_undo_snapshot_no_snapshots() -> Result<()> {
        // Setup
        let ctx = TestContext::new().await?;
        
        // Test steps
        ctx.write_content("test content").await?;
        let result = ctx.undo_snapshot().await;
        
        // Verify
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("No snapshots found"));

        Ok(())
    }

    #[tokio::test]
    async fn test_multiple_snapshots() -> Result<()> {
        // Setup
        let ctx = TestContext::new().await?;
        
        // Test steps - create and modify file multiple times
        ctx.write_content("Initial content").await?;
        ctx.create_snapshot().await?;
        
        ctx.write_content("Second content").await?;
        ctx.create_snapshot().await?;
        
        ctx.write_content("Final content").await?;
        ctx.undo_snapshot().await?;
        
        // Verify - should restore to second version
        assert_eq!(ctx.read_content().await?, "Second content");

        Ok(())
    }

    #[tokio::test]
    async fn test_multiple_snapshots_undo_twice() -> Result<()> {
        // Setup
        let ctx = TestContext::new().await?;
        
        // Test steps - create and modify file multiple times
        ctx.write_content("Initial content").await?;
        ctx.create_snapshot().await?;
        
        ctx.write_content("Second content").await?;
        ctx.create_snapshot().await?;
        
        ctx.write_content("Final content").await?;
        ctx.undo_snapshot().await?;
        ctx.undo_snapshot().await?;

        // Verify - should restore to Initial version
        assert_eq!(ctx.read_content().await?, "Initial content");

        Ok(())
    }
}
