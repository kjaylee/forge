use std::cmp;
use std::path::Path;

use anyhow::{Context, Result};

use crate::error::Error;
use crate::file_info::FileInfo;

impl crate::ForgeFS {
    /// Reads a specific range of lines from a file.
    ///
    /// Returns a tuple containing:
    /// - The file content as a UTF-8 string.
    /// - FileInfo containing metadata about the read operation including line
    ///   positions.
    pub async fn read_range_utf8<T: AsRef<Path>>(
        path: T,
        start_line: u64,
        end_line: u64,
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

        // Split content into lines for processing
        let lines: Vec<&str> = content.lines().collect();
        let total_lines = lines.len() as u64;

        // Validate and normalize the line range
        let (start_pos, end_pos) =
            Self::validate_line_range_bounds(total_lines, start_line, end_line)?;
        let info = FileInfo::new(start_pos, end_pos, total_lines);

        // Return empty result for empty ranges
        if start_pos == end_pos {
            return Ok((String::new(), info));
        }

        // Extract the requested line range
        let result_content = if start_pos == 0 && end_pos == total_lines {
            content // Return the full content if requesting the entire file
        } else {
            let mut result = Vec::new();
            for line_idx in start_pos..end_pos {
                if let Some(line) = lines.get(line_idx as usize) {
                    result.push(*line);
                }
            }
            result.join("\n")
        };

        Ok((result_content, info))
    }

    // Validate the requested range and ensure it falls within the file's line
    // count
    fn validate_line_range_bounds(
        total_lines: u64,
        start_pos: u64,
        end_pos: u64,
    ) -> Result<(u64, u64)> {
        // Check if start is beyond file size
        if start_pos > total_lines {
            return Err(Error::StartBeyondFileSize { start: start_pos, total: total_lines }.into());
        }

        // Cap end position at file size
        let end_pos = cmp::min(end_pos, total_lines);

        // Check if start is greater than end
        if start_pos > end_pos {
            return Err(Error::StartGreaterThanEnd { start: start_pos, end: end_pos }.into());
        }

        Ok((start_pos, end_pos))
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
    async fn test_read_range_utf8() -> Result<()> {
        let content =
            "Line 0\nLine 1\nLine 2\nLine 3\nLine 4\nLine 5\nLine 6\nLine 7\nLine 8\nLine 9";
        let file = create_test_file(content).await?;

        // Test reading a range of lines
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 2, 5).await?;

        assert_eq!(
            result, "Line 2\nLine 3\nLine 4",
            "Lines 2-5 should be Line 2, 3, 4"
        );
        assert_eq!(info.start_line, 2);
        assert_eq!(info.end_line, 5);
        assert_eq!(info.total_lines, 10);

        // Test reading from start
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 0, 3).await?;

        assert_eq!(
            result, "Line 0\nLine 1\nLine 2",
            "Lines 0-3 should be Line 0, 1, 2"
        );
        assert_eq!(info.start_line, 0);
        assert_eq!(info.end_line, 3);

        // Test reading to end
        let total_lines = 10;
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 7, total_lines).await?;

        assert_eq!(
            result, "Line 7\nLine 8\nLine 9",
            "Lines 7-end should be Line 7, 8, 9"
        );
        assert_eq!(info.start_line, 7);
        assert_eq!(info.end_line, info.total_lines);

        // Test reading entire file
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 0, total_lines).await?;

        assert_eq!(
            result, content,
            "Reading entire file should match original content"
        );
        assert_eq!(info.start_line, 0);
        assert_eq!(info.end_line, info.total_lines);

        // Test empty range
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 5, 5).await?;

        assert_eq!(result, "", "Empty range should return empty string");
        assert_eq!(info.start_line, 5);
        assert_eq!(info.end_line, 5);

        // Test invalid ranges
        assert!(
            crate::ForgeFS::read_range_utf8(file.path(), 8, 5)
                .await
                .is_err(),
            "Start > end should error"
        );
        assert!(
            crate::ForgeFS::read_range_utf8(file.path(), 15, total_lines)
                .await
                .is_err(),
            "Start beyond file size should error"
        );

        Ok(())
    }

    #[tokio::test]
    async fn test_utf8_multi_line_handling() -> Result<()> {
        let content = "Hello world!\nこんにちは 世界!\nПривет мир!\nBonjour le monde!";
        let file = create_test_file(content).await?;

        // Test reading a range that includes multi-byte characters
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 1, 3).await?;

        // Line-based indexing should handle multi-byte characters correctly
        assert_eq!(
            result, "こんにちは 世界!\nПривет мир!",
            "Should read exactly the specified lines with multi-byte characters"
        );
        assert_eq!(info.start_line, 1);
        assert_eq!(info.end_line, 3);

        Ok(())
    }
}
