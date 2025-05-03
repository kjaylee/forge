use std::{path::PathBuf, sync::Arc};

use crate::{
    temp_writer::TempWriter,
    truncator::{TruncationResult, Truncator},
    Infrastructure,
};

/// Manages large content by combining truncation and temporary file storage.
///
/// This struct provides a unified interface for:
/// 1. Truncating content according to a specified strategy
/// 2. Storing the full content in a temporary file for later access
/// 3. Retrieving both the truncated view and information about the full content
pub struct ContentManager<F> {
    temp_writer: TempWriter<F>,
}

/// Result of a content management operation
#[derive(Debug)]
pub struct ManagedContent {
    /// The truncated content according to the applied truncation strategy
    pub truncated: TruncationResult,
    /// Path to the temporary file containing the full content
    pub temp_file_path: Option<PathBuf>,
}

impl<F: Infrastructure> ContentManager<F> {
    /// Creates a new ContentManager with the given infrastructure
    pub fn new(infra: Arc<F>) -> Self {
        Self { temp_writer: TempWriter::new(infra) }
    }

    /// Processes content by truncating it and storing the full version in a temporary file if it's truncated
    pub async fn process<S: AsRef<str>>(
        &self,
        truncator: Truncator,
        content: S,
    ) -> anyhow::Result<ManagedContent> {
        let content_str = content.as_ref();

        // Apply truncation
        let truncated = truncator.apply(content_str);

        if truncated.is_truncated() {
            let temp_file_path = self.temp_writer.write(content_str).await?;
            return Ok(ManagedContent { truncated, temp_file_path: Some(temp_file_path) });
        }

        return Ok(ManagedContent { truncated, temp_file_path: None });
    }
}
