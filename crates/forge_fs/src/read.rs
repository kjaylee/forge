use std::path::Path;

use anyhow::{Context, Result};
use tokio::io::AsyncReadExt;

impl crate::ForgeFS {
    pub async fn read_utf8<T: AsRef<Path>>(path: T, max_limit: u64) -> Result<String> {
        Self::read(path, max_limit)
            .await
            .map(|bytes| String::from_utf8_lossy(&bytes).to_string())
    }

    pub async fn read<T: AsRef<Path>>(path: T, max_limit: u64) -> Result<Vec<u8>> {
        let mut file = tokio::fs::File::open(path.as_ref())
            .await
            .with_context(|| format!("Failed to open file {}", path.as_ref().display()))?;
        if let Ok(metadata) = file.metadata().await {
            if metadata.len() > max_limit {
                return Err(anyhow::anyhow!(
                    "File size exceeds maximum limit: {} > {}",
                    metadata.len(),
                    max_limit
                ));
            }
        }

        let mut buffer = vec![];

        file.read_to_end(&mut buffer)
            .await
            .with_context(|| format!("Failed to read file {}", path.as_ref().display()))?;

        Ok(buffer)
    }
}
