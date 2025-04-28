use std::path::Path;

use anyhow::{Context, Result};
use tokio::fs::File;
use tokio::io::AsyncReadExt;

/// Functions for binary file detection
impl crate::ForgeFS {
    /// Checks if a file is binary using the infer crate and additional
    /// heuristics.
    /// 
    /// Returns a tuple containing:
    /// - A boolean indicating if the file is binary
    /// - A string describing the detected file type (if binary)
    ///
    /// This detection uses a multi-step approach:
    /// 1. Use infer to detect known binary formats based on file signatures
    /// 2. Perform a statistical analysis of control characters (fallback)
    /// 3. Validate UTF-8 encoding as a final check
    pub async fn is_binary_file<T: AsRef<Path>>(path: T) -> Result<(bool, String)> {
        let path_ref = path.as_ref();
        
        // Read a sample from the beginning of the file to detect its type
        // The infer crate typically needs less than 8KB for detection
        let mut file = File::open(path_ref)
            .await
            .with_context(|| format!("Failed to open file {}", path_ref.display()))?;

        // Read up to 8KB for file type detection
        let mut sample = vec![0; 8192];
        let bytes_read = file.read(&mut sample).await.with_context(|| {
            format!("Failed to read sample from file {}", path_ref.display())
        })?;
        sample.truncate(bytes_read);

        // Empty files are not binary
        if bytes_read == 0 {
            return Ok((false, String::from("Empty file")));
        }

        // STEP 1: Use infer for content-based type detection
        if let Some(file_type) = infer::get(&sample) {
            // Consider file types based on their category
            match file_type.matcher_type() {
                // Plain text formats and documents are considered non-binary
                infer::MatcherType::Text | infer::MatcherType::Doc => {
                    return Ok((false, file_type.mime_type().to_string()));
                },
                
                // Any other type is considered binary (images, audio, video, archives, etc.)
                _ => {
                    return Ok((true, file_type.mime_type().to_string()));
                }
            }
        }

        // STEP 2: Statistical analysis for unknown formats
        // Count null bytes and control characters (excluding common whitespace)
        let binary_threshold = 0.08; // 8% of content is binary chars = binary file
        let binary_chars = sample
            .iter()
            .filter(|&&b| {
                // Consider control characters (except common whitespace) as binary indicators
                b == 0 || (b < 32 && b != b'\n' && b != b'\r' && b != b'\t' && b != 12) // 12 is form feed
            })
            .count();
        
        let binary_ratio = if bytes_read > 0 {
            binary_chars as f64 / bytes_read as f64
        } else {
            0.0
        };

        if binary_ratio > binary_threshold {
            return Ok((true, format!("Binary data (statistical detection: {}% binary characters)", (binary_ratio * 100.0) as u8)));
        }

        // STEP 3: Attempt UTF-8 validation as a final check
        if String::from_utf8(sample.clone()).is_err() {
            return Ok((true, String::from("Non-UTF8 encoded data")));
        }

        // If we've made it here, the file is likely text-based
        Ok((false, String::from("Text file (no specific format detected)")))
    }
}

#[cfg(test)]
mod test {
    use anyhow::Result;
    use tokio::fs;

    // Helper to create a temporary file with test content
    async fn create_test_file(content: &[u8]) -> Result<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new()?;
        fs::write(file.path(), content).await?;
        Ok(file)
    }

    #[tokio::test]
    async fn test_is_binary_file() -> Result<()> {
        // Test with a text file
        let text_file = create_test_file(b"Hello, world!").await?;
        let (is_binary, _) = crate::ForgeFS::is_binary_file(text_file.path()).await?;
        assert!(!is_binary, "Text file incorrectly identified as binary");

        // Test with a binary file (with null bytes)
        let binary_content = vec![0, 1, 2, 3, 0, 0, 0, 0, 5, 6, 7, 8];
        let binary_file = create_test_file(&binary_content).await?;
        let (is_binary, file_type) = crate::ForgeFS::is_binary_file(binary_file.path()).await?;
        assert!(is_binary, "Binary file not correctly identified");
        assert!(file_type.contains("Binary data"), "Binary file type description not correct");

        // Create a simple PNG image file (with valid PNG header)
        let png_header = [
            0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, // PNG signature
            0x00, 0x00, 0x00, 0x0D, // IHDR chunk length
            0x49, 0x48, 0x44, 0x52, // "IHDR"
            0x00, 0x00, 0x00, 0x01, // width = 1
            0x00, 0x00, 0x00, 0x01, // height = 1
            0x08, 0x02, 0x00, 0x00, 0x00, // bit depth, color type, etc.
        ];
        let png_file = create_test_file(&png_header).await?;
        let (is_binary, file_type) = crate::ForgeFS::is_binary_file(png_file.path()).await?;
        assert!(is_binary, "PNG file not identified as binary");
        assert!(file_type.contains("image/png"), "PNG file type not correctly identified");

        // Test with empty file
        let empty_file = create_test_file(&[]).await?;
        let (is_binary, _) = crate::ForgeFS::is_binary_file(empty_file.path()).await?;
        assert!(!is_binary, "Empty file incorrectly identified as binary");

        Ok(())
    }
}
