use std::path::Path;

use dissimilar::Chunk;
use forge_domain::{NamedTool, ToolCallService, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::Deserialize;
use thiserror::Error;
use tokio::fs;
use tracing::{debug, error};

use crate::fs::syn;

#[derive(Deserialize, JsonSchema)]
pub struct FSReplaceInput {
    /// The path of the file to modify (relative to the current working
    /// directory)
    pub path: String,
    /// Optional content to find in the file. Can be multiple lines.
    /// If None or Some(""), the replacement text will be appended to the end of
    /// the file.
    pub search: Option<String>,
    /// The new content to replace the matched text with. Can be multiple lines.
    /// If empty, the matched text will be deleted.
    pub replace: String,
    /// Whether to replace all occurrences (true) or just the first one (false).
    /// Defaults to false if not specified.
    pub replace_all: Option<bool>,
}

/// Replace or delete content in a file, with support for:
/// - Exact and fuzzy matching for search patterns
/// - Replacing matched content with new content
/// - Deleting matched content (using empty replacement)
/// - Appending content when no search pattern is provided
///
/// For supported file types (.rs, .js, .py, etc.), performs syntax validation
/// on the modified content and returns warnings for invalid syntax.
#[derive(ToolDescription)]
pub struct FSReplace;

#[derive(Debug, Error, PartialEq)]
pub enum Error {
    #[error("No matching content found to replace")]
    NoMatch,

    #[error("Invalid replacement: {0}")]
    InvalidReplacement(String),

    #[error("I/O error: {0}")]
    IO(String),
}

impl NamedTool for FSReplace {
    fn tool_name(&self) -> ToolName {
        ToolName::new("tool_forge_fs_replace")
    }
}

fn normalize_line_endings(text: &str) -> String {
    // Only normalize CRLF to LF while preserving the original line endings
    let mut result = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\r' && chars.peek() == Some(&'\n') {
            chars.next(); // Skip the \n since well add it below
            result.push('\n');
        } else {
            result.push(c);
        }
    }
    result
}

fn replace_text(
    content: &str,
    search: &str,
    replace: &str,
    replace_all: bool,
) -> Result<(String, usize), Error> {
    let mut replacements = 0;
    let normalized_search = normalize_line_endings(search);
    let mut current_text = content.to_string();

    loop {
        // Try exact match first
        if let Some(start_idx) = current_text.find(&normalized_search) {
            let end_idx = start_idx + normalized_search.len();
            current_text.replace_range(start_idx..end_idx, replace);
            replacements += 1;
            if !replace_all {
                break;
            }
            continue;
        }

        // If exact match fails, try fuzzy matching
        let normalized_text = normalize_line_endings(&current_text);
        if let Some(start_idx) = normalized_text.find(&normalized_search) {
            let end_idx = start_idx + normalized_search.len();
            current_text.replace_range(start_idx..end_idx, replace);
            replacements += 1;
            if !replace_all {
                break;
            }
            continue;
        }

        // If still no match, try more aggressive fuzzy matching
        let chunks = dissimilar::diff(&current_text, &normalized_search);
        let mut best_match = None;
        let mut best_score = 0.0;
        let mut current_pos = 0;

        for chunk in chunks.iter() {
            if let Chunk::Equal(text) = chunk {
                let score = text.len() as f64 / normalized_search.len() as f64;
                if score > best_score {
                    best_score = score;
                    best_match = Some((current_pos, text.len()));
                }
            }
            match chunk {
                Chunk::Equal(text) | Chunk::Delete(text) | Chunk::Insert(text) => {
                    current_pos += text.len();
                }
            }
        }

        if let Some((start_idx, len)) = best_match {
            if best_score > 0.7 {
                // Threshold for fuzzy matching
                current_text.replace_range(start_idx..start_idx + len, replace);
                replacements += 1;
                if !replace_all {
                    break;
                }
                continue;
            }
        }

        // No more matches found
        break;
    }

    Ok((current_text, replacements))
}

fn replace_content(
    content: &str,
    search: Option<&str>,
    replace: &str,
    replace_all: bool,
) -> Result<String, Error> {
    // Handle append mode (no search pattern)
    match search {
        None | Some("") => {
            let mut result = content.to_string();
            result.push_str(replace);
            Ok(result)
        }
        Some(search_str) => {
            let (result, replacements) = replace_text(content, search_str, replace, replace_all)?;
            if replacements == 0 {
                Err(Error::NoMatch)
            } else {
                Ok(result)
            }
        }
    }
}

#[async_trait::async_trait]
impl ToolCallService for FSReplace {
    type Input = FSReplaceInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        let replace_all = input.replace_all.unwrap_or(false);

        // Read existing content or use empty string for new files
        let current_content = if Path::new(&input.path).exists() {
            fs::read_to_string(&input.path).await.map_err(|e| {
                error!("Failed to read file content: {}", e);
                Error::IO(format!("Failed to read file: {}", e)).to_string()
            })?
        } else if input.search.as_ref().is_some_and(|s| !s.is_empty()) {
            return Err(Error::InvalidReplacement(
                "File does not exist and search pattern is not empty".to_string(),
            )
            .to_string());
        } else {
            String::new()
        };

        // Apply replacements
        let new_content = match replace_content(
            &current_content,
            input.search.as_deref(),
            &input.replace,
            replace_all,
        ) {
            Ok(content) => content,
            Err(e) => return Err(e.to_string()),
        };

        // Write the modified content
        fs::write(&input.path, &new_content).await.map_err(|e| {
            error!("Failed to write file: {}", e);
            Error::IO(format!("Failed to write file: {}", e)).to_string()
        })?;

        debug!("Successfully wrote changes to {:?}", &input.path);

        // Check syntax and build response
        let syntax_warning = syn::validate(&input.path, &new_content);
        let mut result = format!("Successfully applied changes to {}", input.path);
        if let Some(warning) = syntax_warning {
            result.push_str("\nWarning: ");
            result.push_str(&warning.to_string());
        }

        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use tempfile::TempDir;

    use super::*;

    async fn write_test_file(path: impl AsRef<Path>, content: &str) -> Result<(), String> {
        fs::write(&path, content).await.map_err(|e| e.to_string())
    }

    #[test]
    fn test_replace_content_exact_match() {
        let content = "Hello World\nTest Line\nHello World\n";
        let result = replace_content(content, Some("Hello World"), "Hi World", false);
        assert_eq!(
            result.unwrap(),
            "Hi World\nTest Line\nHello World\n".to_string()
        );
    }

    #[test]
    fn test_replace_content_all() {
        let content = "Hello World\nTest Line\nHello World\n";
        let result = replace_content(content, Some("Hello World"), "Hi World", true);
        assert_eq!(
            result.unwrap(),
            "Hi World\nTest Line\nHi World\n".to_string()
        );
    }

    #[test]
    fn test_replace_content_empty_search() {
        let content = "Hello World\n";
        let result = replace_content(content, None, "New Content", false);
        assert_eq!(result.unwrap(), "Hello World\nNew Content".to_string());
    }

    #[test]
    fn test_replace_content_no_match() {
        let content = "Hello World\n";
        let result = replace_content(content, Some("Non-existent"), "New Content", false);
        assert_eq!(result.unwrap_err(), Error::NoMatch);
    }

    #[test]
    fn test_replace_content_fuzzy_match() {
        let content = "function test() {\n  let x = 1;\n  return x;\n}\n";
        let result = replace_content(
            content,
            Some("let x = 1;\n  return x;"),
            "let x = 2;\n  return x + 1;",
            false,
        );
        assert_eq!(
            result.unwrap(),
            "function test() {\n  let x = 2;\n  return x + 1;\n}\n".to_string()
        );
    }

    #[test]
    fn test_replace_content_with_whitespace() {
        let content = "    Hello World    \n  Test Line  \n";
        let result = replace_content(
            content,
            Some("    Hello World    "),
            "    Hi World    ",
            false,
        );
        assert_eq!(
            result.unwrap(),
            "    Hi World    \n  Test Line  \n".to_string()
        );
    }

    #[test]
    fn test_replace_content_error_handling() {
        let content = "Hello World\n";

        // Test no matches
        let result = replace_content(content, Some("Non-existent"), "New Content", false);
        assert_eq!(result.unwrap_err(), Error::NoMatch);

        // Test empty string search (should work, appends to end)
        let result = replace_content(content, Some(""), "append this", false);
        assert_eq!(result.unwrap(), "Hello World\nappend this");
    }

    #[test]
    fn test_replace_content_deletion() {
        let content = "Hello World\nTest Line\nHello World\n";
        
        // Test single deletion
        let result = replace_content(content, Some("Hello World\n"), "", false);
        assert_eq!(result.unwrap(), "Test Line\nHello World\n");

        // Test all deletions
        let result = replace_content(content, Some("Hello World\n"), "", true);
        assert_eq!(result.unwrap(), "Test Line\n");
    }

    #[tokio::test]
    async fn test_whitespace_preservation() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "    Hello World    \n  Test Line  \n    Hello World    \n";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some("    Hello World    ".to_string()),
                replace: "    Hi World    ".to_string(),
                replace_all: None,
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));
        assert!(result.contains(&file_path.display().to_string()));
    }

    #[tokio::test]
    async fn test_empty_search_new_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        write_test_file(&file_path, "").await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: None,
                replace: "New content\n".to_string(),
                replace_all: None,
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));
        assert!(result.contains(&*file_path.to_string_lossy()));
    }

    #[tokio::test]
    async fn test_replace_all() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "let x = 1;\nlet y = 1;\nlet z = 1;\n";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some(" = 1;".to_string()),
                replace: " = 2;".to_string(),
                replace_all: Some(true),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));

        let content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(content, "let x = 2;\nlet y = 2;\nlet z = 2;\n");
    }

    #[tokio::test]
    async fn test_replace_first_only() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "let x = 1;\nlet y = 1;\nlet z = 1;\n";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some(" = 1;".to_string()),
                replace: " = 2;".to_string(),
                replace_all: Some(false),
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));

        let content = fs::read_to_string(&file_path).await.unwrap();
        assert_eq!(content, "let x = 2;\nlet y = 1;\nlet z = 1;\n");
    }

    #[tokio::test]
    async fn test_fuzzy_search_replace() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        let content = r#"function calculateTotal(items) {
  let total = 0;
  for (const itm of items) {
    total += itm.price;
  }
  return total;
}
"#;
        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some("  for (const itm of items) {\n    total += itm.price;".to_string()),
                replace: "  for (const item of items) {\n    total += item.price * item.quantity;"
                    .to_string(),
                replace_all: None,
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));
        assert!(result.contains(&file_path.display().to_string()));
    }

    #[tokio::test]
    async fn test_invalid_rust_replace() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.rs");
        let content = "fn main() { let x = 42; }";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some("fn main() { let x = 42; }".to_string()),
                replace: "fn main() { let x = ".to_string(),
                replace_all: None,
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));
        assert!(result.contains(&file_path.display().to_string()));
        assert!(result.contains("Warning: Syntax"));
    }

    #[tokio::test]
    async fn test_valid_rust_replace() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.rs");
        let content = "fn main() { let x = 42; }";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some("fn main() { let x = 42; }".to_string()),
                replace: "fn main() { let x = 42; let y = x * 2; }".to_string(),
                replace_all: None,
            })
            .await
            .unwrap();

        assert!(result.contains("Successfully applied"));
        assert!(result.contains(&file_path.display().to_string()));
    }

    #[tokio::test]
    async fn test_no_match_found() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = "Hello World";

        write_test_file(&file_path, content).await.unwrap();

        let fs_replace = FSReplace;
        let result = fs_replace
            .call(FSReplaceInput {
                path: file_path.to_string_lossy().to_string(),
                search: Some("Non-existent content".to_string()),
                replace: "New content".to_string(),
                replace_all: None,
            })
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("No matching content found"));
    }
}
