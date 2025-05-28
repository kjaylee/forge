mod file_loader;

use std::path::Path;

pub use file_loader::*;

/// Loader trait for loading documents
#[async_trait::async_trait]
pub trait Loader: Send + Sync {
    type Output;
    async fn load(&self, path: &Path) -> anyhow::Result<Self::Output>;
}
