use std::path::Path;

use anyhow::Result;
use forge_app::EnvironmentService;
use forge_services::{FsReadService, Infrastructure};

pub struct ForgeFileReadService {
    max_limit: u64,
}

impl ForgeFileReadService {
    pub fn new(infra: &impl Infrastructure) -> Self {
        Self {
            max_limit: infra.environment_service().get_environment().max_read_size,
        }
    }

    pub fn new_with_limit(max_limit: u64) -> Self {
        Self { max_limit }
    }
}

#[async_trait::async_trait]
impl FsReadService for ForgeFileReadService {
    async fn read_utf8(&self, path: &Path) -> Result<String> {
        forge_fs::ForgeFS::read_utf8(path, self.max_limit).await
    }

    async fn read(&self, path: &Path) -> Result<Vec<u8>> {
        forge_fs::ForgeFS::read(path, self.max_limit).await
    }

    async fn range_read_utf8(
        &self,
        path: &Path,
        start_line: u64,
        end_line: u64,
    ) -> Result<(String, forge_fs::FileInfo)> {
        forge_fs::ForgeFS::read_range_utf8(path, start_line, end_line, self.max_limit).await
    }
}
