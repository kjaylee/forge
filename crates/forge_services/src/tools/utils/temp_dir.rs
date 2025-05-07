use std::path::PathBuf;

use anyhow::Context;

pub struct TempDir {
    temp_dir: tempfile::TempDir,
}

impl TempDir {
    const START_MARKER: &'static str = "___START___";
    const END_MARKER: &'static str = "___END___";
    pub fn new() -> anyhow::Result<Self> {
        let temp_dir = Self::temp_dir()?;
        Ok(Self {
            temp_dir: tempfile::Builder::new()
                .prefix(Self::START_MARKER)
                .suffix(Self::END_MARKER)
                .tempdir_in(temp_dir.clone())
                .with_context(|| {
                    format!("failed to create temp directory in: {}", temp_dir.display())
                })?,
        })
    }

    pub fn path(&self) -> std::path::PathBuf {
        self.temp_dir.path().to_path_buf()
    }

    fn temp_dir() -> anyhow::Result<PathBuf> {
        Ok(std::env::temp_dir().canonicalize()?)
    }

    pub fn normalize_entire_path(input: &str) -> String {
        // Super simple: just replace any path with [TEMP_DIR] and keep the filename
        if let Some(last_slash) = input.rfind('/') {
            let file_part = &input[last_slash..];
            return format!("[TEMP_DIR]{}", file_part);
        }
        input.to_string()
    }

    /// Use this function to remove the temporary directory path from the
    /// content
    pub fn normalize(input: &str) -> String {
        let pattern = format!(
            "{}/{}.*{}",
            Self::temp_dir().unwrap().display(),
            Self::START_MARKER,
            Self::END_MARKER
        );
        let pattern = regex::Regex::new(&pattern).unwrap();
        let content = pattern.replace_all(input, "[TEMP_DIR]");

        content.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize_entire_path() {
        // Test with a simple file path
        let path = TempDir::temp_dir().unwrap().join("file.txt");
        assert_eq!(
            TempDir::normalize_entire_path(&path.display().to_string()),
            "[TEMP_DIR]/file.txt"
        );
        
        // Test with a path that includes line number
        let path_with_line = format!("{}/file.txt:1:", TempDir::temp_dir().unwrap().display());
        assert_eq!(
            TempDir::normalize_entire_path(&path_with_line),
            "[TEMP_DIR]/file.txt:1:"
        );
    }
}
