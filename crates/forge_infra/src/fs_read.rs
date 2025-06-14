use std::path::Path;

use anyhow::Result;
use forge_services::FsReadService;

#[derive(Default)]
pub struct ForgeFileReadService {}

impl Default for ForgeFileReadService {
    fn default() -> Self {
        Self::new()
    }
}

impl ForgeFileReadService {
    pub fn new() -> Self {
        Self {}
    }
}

#[async_trait::async_trait]
impl FsReadService for ForgeFileReadService {
    async fn read_utf8(&self, path: &Path, max_size: u64) -> Result<String> {
        forge_fs::ForgeFS::read_utf8(path, max_size).await
    }

    async fn read(&self, path: &Path, max_size: u64) -> Result<Vec<u8>> {
        forge_fs::ForgeFS::read(path, max_size).await
    }

    async fn range_read_utf8(
        &self,
        path: &Path,
        start_line: u64,
        end_line: u64,
        max_size: u64,
    ) -> Result<(String, forge_fs::FileInfo)> {
        forge_fs::ForgeFS::read_range_utf8(path, start_line, end_line, max_size).await
    }
}
