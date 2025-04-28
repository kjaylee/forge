use std::path::Path;

use anyhow::Result;
use forge_services::FsReadService;

pub struct ForgeFileReadService;

impl Default for ForgeFileReadService {
    fn default() -> Self {
        Self
    }
}

impl ForgeFileReadService {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait::async_trait]
impl FsReadService for ForgeFileReadService {
    async fn read(&self, path: &Path) -> Result<String> {
        forge_fs::ForgeFS::read_utf8(path).await
    }

    async fn range_read(
        &self,
        path: &Path,
        start_byte: Option<u64>,
        end_byte: Option<u64>,
    ) -> Result<(String, forge_fs::FileInfo)> {
        forge_fs::ForgeFS::read_range_utf8(path, start_byte, end_byte).await
    }
}
