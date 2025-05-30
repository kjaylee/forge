use anyhow::Context;
use std::path::PathBuf;

/// A cache for storing and retrieving
#[derive(Clone)]
pub struct Cache {
    path: PathBuf,
}

impl TryFrom<PathBuf> for Cache {
    type Error = anyhow::Error;
    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        std::fs::create_dir_all(&path).context("failed to create cache directory")?;
        Ok(Self { path })
    }
}

impl Cache {
    /// Retrieve embeddings from the cache
    pub async fn get(&self, cache_key: &str) -> Option<Vec<f32>> {
        cacache::read(&self.path, cache_key)
            .await
            .map(|cached_bytes| bytemuck::cast_slice(&cached_bytes).to_vec())
            .ok()
    }

    /// Store embeddings in the cache
    pub async fn put(&self, cache_key: &str, cache_value: &[f32]) -> anyhow::Result<()> {
        let bytes: Vec<u8> = bytemuck::cast_slice(cache_value).to_vec();
        cacache::write(&self.path, cache_key, &bytes).await?;
        Ok(())
    }
}
