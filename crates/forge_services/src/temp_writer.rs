use std::{path::PathBuf, sync::Arc};

use crate::{FsWriteService, Infrastructure};

pub struct TempWriter<F> {
    infra: Arc<F>,
}

impl<F: Infrastructure> TempWriter<F> {
    pub fn new(f: Arc<F>) -> Self {
        Self { infra: f }
    }

    /// Writes the content to temp file and returns the path of file.
    pub async fn write<S: AsRef<str>>(
        &self,
        content: S,
    ) -> anyhow::Result<PathBuf> {
        let path = tempfile::Builder::new()
            .keep(true)
            .prefix("forge_")
            .suffix(".txt")
            .tempfile()?
            .into_temp_path()
            .to_path_buf();

        self.infra
            .file_write_service()
            .write(&path, content.as_ref().to_string().into())
            .await?;

        Ok(path)
    }
}
