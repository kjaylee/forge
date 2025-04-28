use std::path::Path;

use anyhow::{Context, Result};
use tokio::fs::File;
use tokio::io::AsyncReadExt;

/// Functions for binary file detection
impl crate::ForgeFS {
    /// Checks if a file is binary using the infer crate and additional
    /// heuristics. Returns a tuple with (is_binary, detected_type) where
    /// detected_type is a string describing the file type if it's binary,
    /// or an empty string if it's not binary.
    pub async fn is_binary_file<T: AsRef<Path>>(path: T) -> Result<(bool, String)> {
        

        // Read a sample from the beginning of the file to detect its type
        let mut file = File::open(path.as_ref())
            .await
            .with_context(|| format!("Failed to open file {}", path.as_ref().display()))?;

        // Read up to 8KB for file type detection
        let mut sample = vec![0; 8192];
        let bytes_read = file.read(&mut sample).await.with_context(|| {
            format!(
                "Failed to read sample from file {}",
                path.as_ref().display()
            )
        })?;
        sample.truncate(bytes_read);

        // Use infer to detect file type
        if let Some(file_type) = infer::get(&sample) {
            // Check if this is a type we consider binary
            // Only consider text and document types as non-binary
            let matcher_type = file_type.matcher_type();
            if matcher_type != infer::MatcherType::Text && matcher_type != infer::MatcherType::Doc {
                return Ok((true, file_type.mime_type().to_string()));
            }
        }

        // Secondary check: Count the occurrence of null bytes and control characters
        // which typically indicate binary content
        let binary_threshold = 0.1; // 10% of content is binary chars = binary file
        let binary_chars = sample
            .iter()
            .filter(|&&b| b == 0 || (b < 32 && b != b'\n' && b != b'\r' && b != b'\t'))
            .count();
        let binary_ratio = binary_chars as f64 / sample.len() as f64;

        if binary_ratio > binary_threshold {
            return Ok((true, "binary/unknown".to_string()));
        }

        // Attempt UTF-8 validation as a final check
        if String::from_utf8(sample.clone()).is_err() {
            return Ok((true, "non-utf8".to_string()));
        }

        Ok((false, String::new()))
    }
}

#[cfg(test)]
mod test {
    use anyhow::Result;
    
    use tokio::fs;

    

    // Helper to create a temporary file with test content
    async fn create_test_file(content: &str) -> Result<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new()?;
        fs::write(file.path(), content).await?;
        Ok(file)
    }

    #[tokio::test]
    async fn test_is_binary_file() -> Result<()> {
        // Test with a text file
        let text_file = create_test_file("Hello, world!").await?;
        let (is_binary, _) = crate::ForgeFS::is_binary_file(text_file.path()).await?;
        assert!(!is_binary, "Text file incorrectly identified as binary");

        // Test with a binary-like file (with null bytes)
        let binary_content = vec![0, 1, 2, 3, 0, 0, 0, 0, 5, 6, 7, 8];
        let binary_file = tempfile::NamedTempFile::new()?;
        fs::write(binary_file.path(), &binary_content).await?;

        let (is_binary, type_info) = crate::ForgeFS::is_binary_file(binary_file.path()).await?;
        assert!(is_binary, "Binary file not correctly identified");
        assert!(!type_info.is_empty(), "Binary file type info is empty");

        Ok(())
    }
}
