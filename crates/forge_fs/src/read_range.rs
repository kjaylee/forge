use std::cmp;
use std::path::Path;

use anyhow::Result;

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
        start_char: Option<u64>,
        end_char: Option<u64>,
    ) -> Result<(String, FileInfo)> {
        let path_ref = path.as_ref();

        // Ensure the file is not binary
        Self::ensure_not_binary(path_ref).await?;

        // Read the entire file content for character counting
        let full_content = Self::read_utf8(path_ref).await?;
        let total_chars = full_content.chars().count() as u64;

        // Validate and normalize the character range
        let (start_pos, end_pos) =
            Self::validate_char_range_bounds(total_chars, start_char, end_char)?;

        // If the range is empty, return an empty result
        if start_pos == end_pos {
            let info = FileInfo::new(start_pos, start_pos, total_chars);
            return Ok((String::new(), info));
        }

        // Extract the content based on character positions
        let content = if start_pos == 0 && end_pos == total_chars {
            // If requesting the entire file, just return the full content
            full_content
        } else {
            // For a subset of characters, find the corresponding substring
            let mut char_positions = Vec::new();
            // Create a mapping of character indices
            for (idx, _) in full_content.char_indices() {
                char_positions.push(idx);
            }

            // Get the start and end character indices in the string
            let start_idx = if start_pos < char_positions.len() as u64 {
                char_positions[start_pos as usize]
            } else {
                full_content.len() // Default to end if out of bounds
            };

            let end_idx = if end_pos < char_positions.len() as u64 {
                char_positions[end_pos as usize]
            } else {
                full_content.len() // Default to end if out of bounds
            };

            full_content[start_idx..end_idx].to_string()
        };

        // Create file info and return results
        let info = FileInfo::new(start_pos, end_pos, total_chars);

        Ok((content, info))
    }

    // Helper: Ensure the file is not detected as binary
    async fn ensure_not_binary(path: &Path) -> Result<()> {
        let (is_binary, binary_type) = Self::is_binary_file(path).await?;
        if is_binary {
            Err(ForgeFileError::BinaryFileNotSupported(binary_type).into())
        } else {
            Ok(())
        }
    }

    // Helper: Validate the requested range and ensure it falls within the file's
    // character count
    fn validate_char_range_bounds(
        total_chars: u64,
        start_char: Option<u64>,
        end_char: Option<u64>,
    ) -> Result<(u64, u64)> {
        let start_pos = start_char.unwrap_or(0);
        if start_pos > total_chars {
            return Err(ForgeFileError::InvalidRange(format!(
                "Start position {start_pos} is beyond the file size of {total_chars} characters"
            ))
            .into());
        }

        let end_pos = end_char.map_or(total_chars, |e| cmp::min(e, total_chars));

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
        let (result, info) =
            crate::ForgeFS::read_range_utf8(file.path(), Some(10), Some(20)).await?;

        assert_eq!(result, "ABCDEFGHIJ", "Range 10-20 should be ABCDEFGHIJ");
        assert_eq!(info.start_char, 10);
        assert_eq!(info.end_char, 20);
        assert_eq!(info.total_chars, content.len() as u64);

        // Test reading from start
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), None, Some(5)).await?;

        assert_eq!(result, "01234", "Range 0-5 should be 01234");
        assert_eq!(info.start_char, 0);
        assert_eq!(info.end_char, 5);

        // Test reading to end
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), Some(50), None).await?;

        assert_eq!(
            result, "opqrstuvwxyz",
            "Range 50-end should be opqrstuvwxyz"
        );
        assert_eq!(info.start_char, 50);
        assert_eq!(info.end_char, info.total_chars);

        // Test reading entire file
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), None, None).await?;

        assert_eq!(
            result, content,
            "Reading entire file should match original content"
        );
        assert_eq!(info.start_char, 0);
        assert_eq!(info.end_char, info.total_chars);

        // Test empty range
        let (result, info) =
            crate::ForgeFS::read_range_utf8(file.path(), Some(10), Some(10)).await?;

        assert_eq!(result, "", "Empty range should return empty string");
        assert_eq!(info.start_char, 10);
        assert_eq!(info.end_char, 10);

        // Test invalid ranges
        assert!(
            crate::ForgeFS::read_range_utf8(file.path(), Some(20), Some(10))
                .await
                .is_err(),
            "Start > end should error"
        );
        assert!(
            crate::ForgeFS::read_range_utf8(file.path(), Some(1000), None)
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
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), Some(6), Some(8)).await?;

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
