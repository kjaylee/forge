use std::path::Path;

use anyhow::{Context, Result};

use crate::error::Error;
use crate::file_info::FileInfo;

impl crate::ForgeFS {
    /// Reads a specific range of lines from a file.
    ///
    /// Returns a tuple containing:
    /// - The file content as a UTF-8 string for the specified line range.
    /// - FileInfo containing metadata about the read operation.
    ///
    /// Line numbers are 1-based. If start_line is None, defaults to line 1.
    /// If end_line is None, defaults to the last line of the file.
    pub async fn read_range_lines_utf8<T: AsRef<Path>>(
        path: T,
        start_line: Option<u64>,
        end_line: Option<u64>,
    ) -> Result<(String, FileInfo)> {
        let path_ref = path.as_ref();

        // Open the file for binary check
        let mut file = tokio::fs::File::open(path_ref)
            .await
            .with_context(|| format!("Failed to open file {}", path_ref.display()))?;

        // Check if the file is binary
        let (is_text, file_type) = Self::is_binary(&mut file).await?;
        if !is_text {
            return Err(Error::BinaryFileNotSupported(file_type).into());
        }

        // Read the file content
        let content = tokio::fs::read_to_string(path_ref)
            .await
            .with_context(|| format!("Failed to read file content from {}", path_ref.display()))?;

        let lines: Vec<&str> = content.lines().collect();
        let total_lines = lines.len() as u64;

        if total_lines == 0 {
            let info = FileInfo::new(1, 1, 0);
            return Ok((String::new(), info));
        }

        // Validate and normalize line numbers (1-based)
        let actual_start_line = start_line.unwrap_or(1);
        let actual_end_line = end_line.unwrap_or(total_lines);

        // Validate the line range
        Self::validate_line_range_bounds(total_lines, actual_start_line, actual_end_line)?;

        // Extract the requested lines (convert to 0-based indexing)
        let start_idx = (actual_start_line - 1) as usize;
        let end_idx = actual_end_line as usize;

        let result_content = if start_idx < lines.len() {
            let end_idx = std::cmp::min(end_idx, lines.len());
            lines[start_idx..end_idx].join("\n")
        } else {
            String::new()
        };

        let info = FileInfo::new(actual_start_line, actual_end_line, total_lines);

        Ok((result_content, info))
    }

    /// Validates the requested line range and ensures it falls within the
    /// file's line count
    fn validate_line_range_bounds(total_lines: u64, start_line: u64, end_line: u64) -> Result<()> {
        // Check if start is beyond file size
        if start_line > total_lines && total_lines > 0 {
            return Err(
                Error::StartBeyondFileSize { start: start_line, total: total_lines }.into(),
            );
        }

        // Check if start is greater than end
        if start_line > end_line {
            return Err(Error::StartGreaterThanEnd { start: start_line, end: end_line }.into());
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use anyhow::Result;
    use pretty_assertions::assert_eq;
    use tokio::fs;

    // Helper to create a temporary file with test content.
    async fn create_test_file(content: &str) -> Result<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new()?;
        fs::write(file.path(), content).await?;
        Ok(file)
    }

    #[tokio::test]
    async fn test_read_range_lines_utf8() -> Result<()> {
        let content = "Line 1\nLine 2\nLine 3\nLine 4\nLine 5";
        let file = create_test_file(content).await?;

        // Test reading a range of lines
        let (result, info) =
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(2), Some(4)).await?;

        assert_eq!(
            result, "Line 2\nLine 3\nLine 4",
            "Lines 2-4 should be returned"
        );
        assert_eq!(info.start_line, 2);
        assert_eq!(info.end_line, 4);
        assert_eq!(info.total_lines, 5);

        // Test reading from start
        let (result, info) =
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(1), Some(2)).await?;

        assert_eq!(result, "Line 1\nLine 2", "Lines 1-2 should be returned");
        assert_eq!(info.start_line, 1);
        assert_eq!(info.end_line, 2);

        // Test reading to end
        let (result, info) =
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(4), None).await?;

        assert_eq!(result, "Line 4\nLine 5", "Lines 4-end should be returned");
        assert_eq!(info.start_line, 4);
        assert_eq!(info.end_line, 5);

        // Test reading entire file
        let (result, info) = crate::ForgeFS::read_range_lines_utf8(file.path(), None, None).await?;

        assert_eq!(
            result, content,
            "Reading entire file should match original content"
        );
        assert_eq!(info.start_line, 1);
        assert_eq!(info.end_line, 5);

        // Test single line
        let (result, info) =
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(3), Some(3)).await?;

        assert_eq!(result, "Line 3", "Single line should be returned");
        assert_eq!(info.start_line, 3);
        assert_eq!(info.end_line, 3);

        // Test invalid ranges
        assert!(
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(4), Some(2))
                .await
                .is_err(),
            "Start > end should error"
        );
        assert!(
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(10), Some(12))
                .await
                .is_err(),
            "Start beyond file size should error"
        );

        Ok(())
    }

    #[tokio::test]
    async fn test_empty_file() -> Result<()> {
        let content = "";
        let file = create_test_file(content).await?;

        let (result, info) = crate::ForgeFS::read_range_lines_utf8(file.path(), None, None).await?;

        assert_eq!(result, "", "Empty file should return empty string");
        assert_eq!(info.start_line, 1);
        assert_eq!(info.end_line, 1);
        assert_eq!(info.total_lines, 0);

        Ok(())
    }

    #[tokio::test]
    async fn test_single_line_file() -> Result<()> {
        let content = "Single line without newline";
        let file = create_test_file(content).await?;

        let (result, info) = crate::ForgeFS::read_range_lines_utf8(file.path(), None, None).await?;

        assert_eq!(result, content, "Single line file should return the line");
        assert_eq!(info.start_line, 1);
        assert_eq!(info.end_line, 1);
        assert_eq!(info.total_lines, 1);

        Ok(())
    }

    #[tokio::test]
    async fn test_utf8_content() -> Result<()> {
        let content = "Hello 世界!\nこんにちは!\nПривет!";
        let file = create_test_file(content).await?;

        // Test reading a range that includes multi-byte characters
        let (result, info) =
            crate::ForgeFS::read_range_lines_utf8(file.path(), Some(1), Some(2)).await?;

        assert_eq!(
            result, "Hello 世界!\nこんにちは!",
            "Should handle UTF-8 correctly"
        );
        assert_eq!(info.start_line, 1);
        assert_eq!(info.end_line, 2);
        assert_eq!(info.total_lines, 3);

        Ok(())
    }
}
