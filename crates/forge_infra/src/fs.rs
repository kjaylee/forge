use std::path::Path;

use anyhow::{Context, Result};
use forge_app::FileReadService;

pub struct ForgeFileService;

impl Default for ForgeFileService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeFileService {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait::async_trait]
impl FileReadService for ForgeFileService {
    // TODO: add support for file-write operations
    async fn read(&self, path: &Path) -> Result<String> {
        Ok(tokio::fs::read_to_string(path)
            .await
            .with_context(|| format!("Failed to read file: {}", path.display()))?)
    }
}
