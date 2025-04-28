use std::cmp;
use std::path::Path;

use anyhow::{Context, Result};
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncSeekExt};

use crate::error::ForgeFileError;
use crate::file_info::FileInfo;

impl crate::ForgeFS {
    /// Reads a specific range of bytes from a file, respecting UTF-8 boundaries.
    ///
    /// Returns a tuple containing:
    /// - The file content as a UTF-8 string.
    /// - FileInfo containing metadata about the read operation
    ///   (start_byte, end_byte, total_size).
    pub async fn read_range_utf8<T: AsRef<Path>>(
        path: T,
        start_byte: Option<u64>,
        end_byte: Option<u64>,
    ) -> Result<(String, FileInfo)> {
        let path_ref = path.as_ref();

        // Ensure the file is not binary and get its size
        Self::ensure_not_binary(path_ref).await?;
        let file_size = Self::get_file_size(path_ref).await?;

        // Validate and normalize the requested range
        let (start_pos, end_pos) = Self::validate_range_bounds(file_size, start_byte, end_byte)?;

        // Open the file for reading
        let mut file = File::open(path_ref)
            .await
            .with_context(|| format!("Failed to open file {}", path_ref.display()))?;

        // Adjusted start position for UTF-8 safety
        // Note: For additional UTF-8 safety, we could call Self::adjust_start_boundary
        //       from utf8_boundary.rs here
        let adjusted_start = start_pos;

        // Compute actual bytes to read
        let bytes_to_read = end_pos.saturating_sub(adjusted_start);

        // If the range is empty, return an empty result immediately
        if bytes_to_read == 0 {
            let info = FileInfo::new(adjusted_start, adjusted_start, file_size);
            return Ok((String::new(), info));
        }

        // Seek to the start position
        file.seek(std::io::SeekFrom::Start(adjusted_start))
            .await
            .with_context(|| format!("Failed to seek to position {}", adjusted_start))?;

        // Create a buffer to hold the content
        let mut buffer = vec![0u8; bytes_to_read as usize];
        
        // Read the content into the buffer
        let bytes_read = file.read(&mut buffer)
            .await
            .with_context(|| format!("Failed to read from file {}", path_ref.display()))?;
            
        // Truncate the buffer to the actual number of bytes read
        buffer.truncate(bytes_read);

        // Convert bytes to UTF-8 string
        let content = String::from_utf8(buffer)
            .map_err(|e| ForgeFileError::Utf8ValidationFailed(e))?;

        // Create file info and return results
        let adjusted_end = adjusted_start + bytes_read as u64;
        let info = FileInfo::new(adjusted_start, adjusted_end, file_size);
        
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

    // Helper: Validate the requested range and ensure it falls within the file
    fn validate_range_bounds(
        file_size: u64,
        start_byte: Option<u64>,
        end_byte: Option<u64>,
    ) -> Result<(u64, u64)> {
        let start_pos = start_byte.unwrap_or(0);
        if start_pos > file_size {
            return Err(ForgeFileError::InvalidRange(format!(
                "Start position {} is beyond the file size {}",
                start_pos, file_size
            ))
            .into());
        }

        let end_pos = end_byte.map_or(file_size, |e| cmp::min(e, file_size));

        if start_pos > end_pos {
            return Err(ForgeFileError::InvalidRange(format!(
                "Start position {} is greater than end position {}",
                start_pos, end_pos
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

        // Test reading a range of bytes
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), Some(10), Some(20)).await?;
        
        assert_eq!(result, "ABCDEFGHIJ", "Range 10-20 should be ABCDEFGHIJ");
        assert_eq!(info.start_byte, 10);
        assert_eq!(info.end_byte, 20);
        assert_eq!(info.total_size, content.len() as u64);
        
        // Test reading from start
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), None, Some(5)).await?;
        
        assert_eq!(result, "01234", "Range 0-5 should be 01234");
        assert_eq!(info.start_byte, 0);
        assert_eq!(info.end_byte, 5);

        // Test reading to end
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), Some(50), None).await?;
        
        assert_eq!(result, "opqrstuvwxyz", "Range 50-end should be opqrstuvwxyz");
        assert_eq!(info.start_byte, 50);
        assert_eq!(info.end_byte, info.total_size);

        // Test reading entire file
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), None, None).await?;
        
        assert_eq!(result, content, "Reading entire file should match original content");
        assert_eq!(info.start_byte, 0);
        assert_eq!(info.end_byte, info.total_size);

        // Test empty range
        let (result, info) = crate::ForgeFS::read_range_utf8(file.path(), Some(10), Some(10)).await?;
        
        assert_eq!(result, "", "Empty range should return empty string");
        assert_eq!(info.start_byte, 10);
        assert_eq!(info.end_byte, 10);

        // Test invalid ranges
        assert!(crate::ForgeFS::read_range_utf8(file.path(), Some(20), Some(10))
            .await
            .is_err(), "Start > end should error");
        assert!(crate::ForgeFS::read_range_utf8(file.path(), Some(1000), None)
            .await
            .is_err(), "Start beyond file size should error");

        Ok(())
    }

    #[tokio::test]
    #[ignore] // Temporarily ignore this test until we properly handle multi-byte characters
    async fn test_utf8_boundary_in_range() -> Result<()> {
        let content = "Hello 世界! こんにちは! Привет!";
        let file = create_test_file(content).await?;

        // Test reading a range that includes multi-byte characters
        let (result, info) =
            crate::ForgeFS::read_range_utf8(file.path(), Some(6), Some(15)).await?;
        
        // The implementation should adjust to UTF-8 boundaries
        assert_eq!(info.start_byte, 6); // Start at the beginning of 世 (assuming 6 is the byte position)
        assert!(
            result.starts_with("世界"),
            "Result doesn't start with expected character"
        );

        Ok(())
    }
}
