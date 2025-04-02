//! # ForgeFS
//!
//! A file system abstraction layer that standardizes error handling for file
//! operations.
//!
//! ForgeFS wraps tokio's filesystem operations with consistent error context
//! using anyhow::Context. Each method provides standardized error messages in
//! the format "Failed to [operation] [path]", ensuring uniform error reporting
//! throughout the application while preserving the original error cause.

use std::path::Path;

use anyhow::{Context, Result};

pub struct ForgeFS;

impl ForgeFS {
    pub async fn create_dir_all<T: AsRef<Path>>(path: T) -> Result<()> {
        tokio::fs::create_dir_all(path.as_ref())
            .await
            .with_context(|| format!("Failed to create dir {}", path.as_ref().display()))
    }
    pub async fn write<T: AsRef<Path>, U: AsRef<[u8]>>(path: T, contents: U) -> Result<()> {
        tokio::fs::write(path.as_ref(), contents)
            .await
            .with_context(|| format!("Failed to write file {}", path.as_ref().display()))
    }

    pub async fn read_utf8<T: AsRef<Path>>(path: T) -> Result<String> {
        ForgeFS::read(path)
            .await
            .map(|bytes| String::from_utf8_lossy(&bytes).to_string())
    }

    pub async fn read<T: AsRef<Path>>(path: T) -> Result<Vec<u8>> {
        tokio::fs::read(path.as_ref())
            .await
            .with_context(|| format!("Failed to read file {}", path.as_ref().display()))
    }
    pub async fn remove_file<T: AsRef<Path>>(path: T) -> Result<()> {
        tokio::fs::remove_file(path.as_ref())
            .await
            .with_context(|| format!("Failed to remove file {}", path.as_ref().display()))
    }
    pub fn exists<T: AsRef<Path>>(path: T) -> bool {
        path.as_ref().exists()
    }
    pub fn is_file<T: AsRef<Path>>(path: T) -> bool {
        path.as_ref().is_file()
    }

    pub async fn read_dir<T: AsRef<Path>>(path: T) -> Result<tokio::fs::ReadDir> {
        tokio::fs::read_dir(path.as_ref())
            .await
            .with_context(|| format!("Failed to read directory {}", path.as_ref().display()))
    }

    pub async fn read_range<T: AsRef<Path>>(
        path: T,
        start: usize,
        end: usize,
    ) -> Result<(String, usize)> {
        let content = tokio::fs::read_to_string(path.as_ref())
            .await
            .with_context(|| format!("Failed to read file {}", path.as_ref().display()))?;

        let total_lines = content.lines().count();

        if start > total_lines {
            return Err(anyhow::anyhow!(
                "Start line {} exceeds total lines {}",
                start,
                total_lines
            ));
        }

        let end = std::cmp::min(end, total_lines);
        let range_content = content
            .lines()
            .skip(start.saturating_sub(1)) // Convert to 0-based indexing
            .take(end.saturating_sub(start).saturating_add(1))
            .collect::<Vec<&str>>()
            .join("\n");

        Ok((range_content, total_lines))
    }

    pub async fn count_lines<T: AsRef<Path>>(path: T) -> Result<usize> {
        let content = tokio::fs::read_to_string(path.as_ref())
            .await
            .with_context(|| {
                format!(
                    "Failed to read file to count lines: {}",
                    path.as_ref().display()
                )
            })?;

        Ok(content.lines().count())
    }

    pub async fn write_temp<U: AsRef<[u8]>>(content: U, prefix: &str) -> Result<String> {
        let timestamp = chrono::Utc::now().format("%Y%m%d_%H%M%S").to_string();
        let random = rand::random::<u16>();
        let temp_dir = std::env::temp_dir();

        let path = format!(
            "{}/{}_{:04x}_{}.log",
            temp_dir.to_string_lossy(),
            prefix,
            random,
            timestamp
        );

        tokio::fs::write(&path, content)
            .await
            .with_context(|| format!("Failed to write temporary file {}", path))?;

        Ok(path)
    }
}
