use std::cmp;
use std::path::Path;

use anyhow::{Context, Result};

use crate::error::ForgeFileError;
use crate::file_info::FileInfo;

impl crate::ForgeFS {
    /// Reads a specific range of characters from a file.
    ///
    /// Returns a tuple containing:
    /// - The file content as a UTF-8 string.
    /// - FileInfo containing metadata about the read operation including
    ///   character positions.
    pub async fn read_range_utf8<T: AsRef<Path>>(
        path: T,
        start_char: u64,
        end_char: u64,
    ) -> Result<(String, FileInfo)> {
        let path_ref = path.as_ref();

        // Open the file once to get a handle
        let mut file = tokio::fs::File::open(path_ref)
            .await
            .with_context(|| format!("Failed to open file {}", path_ref.display()))?;

        // Skip binary detection in test mode

        // Use our dedicated binary detection function
        let (is_text, file_type) = Self::is_binary(&mut file).await?;

        if !is_text {
            return Err(ForgeFileError::BinaryFileNotSupported(file_type).into());
        }

        // Read the entire file content for character counting using the same file
        // handle
        let mut content = String::new();
        let mut file_reader = tokio::io::BufReader::new(file);
        tokio::io::AsyncReadExt::read_to_string(&mut file_reader, &mut content)
            .await
            .with_context(|| format!("Failed to read file content from {}", path_ref.display()))?;

        let total_chars = content.chars().count() as u64;

        // Validate and normalize the character range
        let (start_pos, end_pos) =
            Self::validate_char_range_bounds(total_chars, start_char, end_char)?;

        // If the range is empty, return an empty result
        if start_pos == end_pos {
            let info = FileInfo::new(start_pos, start_pos, total_chars);
            return Ok((String::new(), info));
        }

        // Extract the content based on character positions
        let result_content = if start_pos == 0 && end_pos == total_chars {
            // If requesting the entire file, just return the full content
            content
        } else {
            // For a subset of characters, find the corresponding substring
            let mut char_positions = Vec::new();
            // Create a mapping of character indices
            for (idx, _) in content.char_indices() {
                char_positions.push(idx);
            }

            // Get the start and end character indices in the string
            let start_idx = if start_pos < char_positions.len() as u64 {
                char_positions[start_pos as usize]
            } else {
                content.len() // Default to end if out of bounds
            };

            let end_idx = if end_pos < char_positions.len() as u64 {
                char_positions[end_pos as usize]
            } else {
                content.len() // Default to end if out of bounds
            };

            content[start_idx..end_idx].to_string()
        };

        // Create file info and return results
        let info = FileInfo::new(start_pos, end_pos, total_chars);

        Ok((result_content, info))
    }

    // Helper functions for binary detection are now inlined in read_range_utf8

    // Helper: Validate the requested range and ensure it falls within the file's
    // character count
    fn validate_char_range_bounds(
        total_chars: u64,
        start_pos: u64,
        end_pos: u64,
    ) -> Result<(u64, u64)> {
        if start_pos > total_chars {
            return Err(ForgeFileError::InvalidRange(format!(
                "Start position {start_pos} is beyond the file size of {total_chars} characters"
            ))
            .into());
        }

        let end_pos = cmp::min(end_pos, total_chars);

        if start_pos > end_pos {
            return Err(ForgeFileError::InvalidRange(format!(
                "Start position {start_pos} is greater than end position {end_pos}"
            ))
            .into());
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
        let content = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        let file = create_test_file(content).await?;

        // Test reading a range of characters
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 10, 20).await?;

        assert_eq!(result, "ABCDEFGHIJ", "Range 10-20 should be ABCDEFGHIJ");
        assert_eq!(info.start_char, 10);
        assert_eq!(info.end_char, 20);
        assert_eq!(info.total_chars, content.len() as u64);

        // Test reading from start
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 0, 5).await?;

        assert_eq!(result, "01234", "Range 0-5 should be 01234");
        assert_eq!(info.start_char, 0);
        assert_eq!(info.end_char, 5);

        // Test reading to end
        let total_chars = content.chars().count() as u64;
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 50, total_chars).await?;

        assert_eq!(
            result, "opqrstuvwxyz",
            "Range 50-end should be opqrstuvwxyz"
        );
        assert_eq!(info.start_char, 50);
        assert_eq!(info.end_char, info.total_chars);

        // Test reading entire file
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 0, total_chars).await?;

        assert_eq!(
            result, content,
            "Reading entire file should match original content"
        );
        assert_eq!(info.start_char, 0);
        assert_eq!(info.end_char, info.total_chars);

        // Test empty range
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 10, 10).await?;

        assert_eq!(result, "", "Empty range should return empty string");
        assert_eq!(info.start_char, 10);
        assert_eq!(info.end_char, 10);

        // Test invalid ranges
        assert!(
            crate::ForgeFS::read_range_utf8(file.path(), 20, 10)
                .await
                .is_err(),
            "Start > end should error"
        );
        assert!(
            crate::ForgeFS::read_range_utf8(file.path(), 1000, total_chars)
                .await
                .is_err(),
            "Start beyond file size should error"
        );

        Ok(())
    }

    #[tokio::test]
    async fn test_utf8_boundary_handling() -> Result<()> {
        let content = "Hello 世界! こんにちは! Привет!";
        let file = create_test_file(content).await?;

        // Test reading a range that includes multi-byte characters
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), 6, 8).await?;

        // Character-based indexing should handle multi-byte characters correctly
        assert_eq!(
            result, "世界",
            "Should read exactly the multi-byte characters"
        );
        assert_eq!(info.start_char, 6);
        assert_eq!(info.end_char, 8);

        Ok(())
    }
}
