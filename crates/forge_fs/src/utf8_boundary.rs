use anyhow::{Context, Result};
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncSeekExt, SeekFrom};

impl crate::ForgeFS {
    /// Adjust the start position to align with UTF-8 character boundary
    pub async fn adjust_start_boundary(file: &mut File, start_pos: u64) -> Result<u64> {
        // If start_pos is 0, no adjustment needed
        if start_pos == 0 {
            return Ok(0);
        }

        // Position file at the desired start
        file.seek(SeekFrom::Start(start_pos))
            .await
            .with_context(|| "Failed to seek to start position")?;

        // Read a small buffer to check if we're at a valid UTF-8 boundary
        let mut sample = [0u8; 4]; // Max UTF-8 character size is 4 bytes
        let bytes_read = file
            .read(&mut sample)
            .await
            .with_context(|| "Failed to read sample for UTF-8 boundary check")?;

        // If we're at EOF, just return the start position
        if bytes_read == 0 {
            return Ok(start_pos);
        }

        // Check if the byte at start_pos is a UTF-8 continuation byte
        if (sample[0] & 0xC0) == 0x80 {
            // This is a continuation byte, need to find the leading byte
            // Move backwards up to 3 bytes to find a non-continuation byte
            let mut adjusted_pos = start_pos;
            for offset in 1..=3 {
                if start_pos < offset {
                    // We're near the beginning of the file
                    adjusted_pos = 0;
                    break;
                }

                // Try reading the byte at this offset
                file.seek(SeekFrom::Start(start_pos - offset))
                    .await
                    .with_context(|| "Failed to seek backward for UTF-8 boundary check")?;

                let mut lead_byte = [0u8; 1];
                file.read_exact(&mut lead_byte)
                    .await
                    .with_context(|| "Failed to read lead byte for UTF-8 boundary check")?;

                // If this is not a continuation byte, we found our boundary
                if (lead_byte[0] & 0xC0) != 0x80 {
                    adjusted_pos = start_pos - offset;
                    break;
                }
            }

            // Reset position to the adjusted position
            file.seek(SeekFrom::Start(adjusted_pos))
                .await
                .with_context(|| "Failed to seek to adjusted start position")?;

            return Ok(adjusted_pos);
        }

        // We're already at a valid UTF-8 boundary
        Ok(start_pos)
    }
}

#[cfg(test)]
mod test {
    use anyhow::Result;
    use pretty_assertions::assert_eq;
    use tokio::fs;
    use tokio::io::AsyncSeekExt;

    use super::*;

    #[tokio::test]
    async fn test_utf8_boundary_adjustment() -> Result<()> {
        // Create a test file with multi-byte UTF-8 characters
        let content = "Hello 世界! こんにちは! Привет!";
        let file = tempfile::NamedTempFile::new()?;
        fs::write(file.path(), content).await?;

        // Open file and seek to different positions
        let mut file = File::open(file.path()).await?;

        // Test middle of ASCII character - should remain unchanged
        let pos = 2; // 'l' in "Hello"
        file.seek(SeekFrom::Start(pos)).await?;
        let adjusted = crate::ForgeFS::adjust_start_boundary(&mut file, pos).await?;
        assert_eq!(
            adjusted, pos,
            "ASCII character position was adjusted unexpectedly"
        );

        // Test middle of multi-byte character - 世 (3 bytes)
        // "Hello " is 6 bytes, 世 starts at byte 6
        // If we start at byte 7 (the middle of 世), it should adjust to byte 6
        let pos = 7;
        file.seek(SeekFrom::Start(pos)).await?;
        let adjusted = crate::ForgeFS::adjust_start_boundary(&mut file, pos).await?;
        assert_eq!(
            adjusted, 6,
            "Multi-byte character position wasn't adjusted correctly"
        );

        // Test at start of multi-byte character - should remain unchanged
        let pos = 6; // start of 世
        file.seek(SeekFrom::Start(pos)).await?;
        let adjusted = crate::ForgeFS::adjust_start_boundary(&mut file, pos).await?;
        assert_eq!(
            adjusted, pos,
            "Start of multi-byte char position was adjusted unexpectedly"
        );

        // Test position 0 - should always return 0
        let pos = 0;
        let adjusted = crate::ForgeFS::adjust_start_boundary(&mut file, pos).await?;
        assert_eq!(adjusted, 0, "Position 0 was adjusted unexpectedly");

        Ok(())
    }
}
