use std::collections::HashSet;
use std::path::Path;

use forge_domain::{Description, ToolCallService};
use forge_tool_macros::Description;
use schemars::JsonSchema;
use serde::Deserialize;

#[derive(Deserialize, JsonSchema)]
pub struct FSSearchInput {
    /// The path of the directory to search in (relative to the current working
    /// directory). This directory will be recursively searched.
    pub path: String,
    /// The regular expression pattern to search for. Uses Rust regex syntax.
    pub regex: String,
    /// Glob pattern to filter files (e.g., '*.ts' for TypeScript files). If not
    /// provided, it will search all files (*).
    pub file_pattern: Option<String>,
}

/// Request to perform a regex search across files in a specified directory,
/// providing context-rich results. This tool searches for patterns or specific
/// content across multiple files, displaying each match with encapsulating
/// context.
#[derive(Description)]
pub struct FSSearch;

#[async_trait::async_trait]
impl ToolCallService for FSSearch {
    type Input = FSSearchInput;
    type Output = Vec<String>;

    async fn call(&self, input: Self::Input) -> Result<Self::Output, String> {
        use regex::Regex;
        use walkdir::WalkDir;

        let dir = Path::new(&input.path);
        if !dir.exists() {
            return Err(format!("Directory '{}' does not exist", input.path));
        }

        // Create regex pattern - case-insensitive by default
        let pattern = format!("(?i){}", input.regex);
        let regex = Regex::new(&pattern).map_err(|e| format!("Invalid regex pattern: {}", e))?;

        let glob_pattern = input.file_pattern.unwrap_or_else(|| "*".to_string());
        let glob = glob::Pattern::new(&glob_pattern)
            .map_err(|e| format!("Invalid glob pattern: {}", e))?;

        let mut matches = Vec::new();
        let mut seen_paths = HashSet::new();

        // Configure walker with proper options
        let walker = WalkDir::new(dir)
            .follow_links(true) // Follow symbolic links
            .same_file_system(true) // Stay on same filesystem
            .into_iter()
            .filter_entry(move |e| {
                if e.file_type().is_dir() {
                    return true; // Always traverse directories
                }
                e.file_name()
                    .to_str()
                    .map(|name| glob.matches(name))
                    .unwrap_or(false)
            });

        for entry in walker.filter_map(Result::ok) {
            let path = entry.path();
            let path_str = path.to_string_lossy();

            // Skip if we've already processed this file
            if !seen_paths.insert(path_str.to_string()) {
                continue;
            }

            // Only process files
            if !entry.file_type().is_file() {
                continue;
            }

            // Try to read the file content
            let content = match tokio::fs::read_to_string(path).await {
                Ok(content) => content,
                Err(e) => {
                    // Skip binary or unreadable files silently
                    if e.kind() != std::io::ErrorKind::InvalidData {
                        matches.push(format!("Error reading {}: {}", path_str, e));
                    }
                    continue;
                }
            };

            let mut found_match = false;
            let lines: Vec<&str> = content.lines().collect();

            // Search through the file content
            for (line_num, line) in lines.iter().enumerate() {
                if regex.is_match(line) {
                    found_match = true;

                    // Get context (3 lines before and after)
                    let start = line_num.saturating_sub(3);
                    let end = (line_num + 4).min(lines.len());

                    // Format the match with location and context
                    let mut match_output =
                        format!("{}:{}:{}\n", path_str, line_num + 1, line.trim());

                    // Add context lines with line numbers
                    for (ctx_num, ctx_line) in lines[start..end].iter().enumerate() {
                        let ctx_line_num = start + ctx_num + 1;
                        if ctx_line_num != line_num + 1 {
                            // Skip the matching line itself
                            match_output.push_str(&format!(
                                "  {}: {}\n",
                                ctx_line_num,
                                ctx_line.trim()
                            ));
                        }
                    }

                    matches.push(match_output);
                }
            }

            // If no content matches but filename matches pattern
            if !found_match && regex.is_match(&path_str) {
                matches.push(format!("{}\n", path_str));
            }
        }

        if matches.is_empty() {
            Ok(vec![format!(
                "No matches found for pattern '{}' in path '{}'",
                input.regex, input.path
            )])
        } else {
            Ok(matches)
        }
    }
}

#[cfg(test)]
mod test {
    use tempfile::TempDir;
    use tokio::fs;

    use super::*;

    #[tokio::test]
    async fn test_fs_search_content() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("test1.txt"), "Hello test world")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("test2.txt"), "Another test case")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("other.txt"), "No match here")
            .await
            .unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 2);
        assert!(result.iter().any(|p| p.contains("test1.txt")));
        assert!(result.iter().any(|p| p.contains("test2.txt")));
    }

    #[tokio::test]
    async fn test_fs_search_with_pattern() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("test1.txt"), "Hello test world")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("test2.rs"), "fn test() {}")
            .await
            .unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: Some("*.rs".to_string()),
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 1);
        assert!(result.iter().any(|p| p.contains("test2.rs")));
    }

    #[tokio::test]
    async fn test_fs_search_with_context() {
        let temp_dir = TempDir::new().unwrap();
        let content = "line 1\nline 2\ntest line\nline 4\nline 5";

        fs::write(temp_dir.path().join("test.txt"), content)
            .await
            .unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 1);
        assert!(result[0].contains("test line"));
        assert!(result[0].contains("line 1"));
        assert!(result[0].contains("line 5"));
    }

    #[tokio::test]
    async fn test_fs_search_recursive() {
        let temp_dir = TempDir::new().unwrap();

        let sub_dir = temp_dir.path().join("subdir");
        fs::create_dir(&sub_dir).await.unwrap();

        fs::write(temp_dir.path().join("test1.txt"), "test content")
            .await
            .unwrap();
        fs::write(sub_dir.join("test2.txt"), "more test content")
            .await
            .unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 2);
        assert!(result.iter().any(|p| p.contains("test1.txt")));
        assert!(result.iter().any(|p| p.contains("test2.txt")));
    }

    #[tokio::test]
    async fn test_fs_search_case_insensitive() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(
            temp_dir.path().join("test.txt"),
            "TEST CONTENT\ntest content",
        )
        .await
        .unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        assert!(result.len() >= 2);
        assert!(result.iter().any(|p| p.contains("TEST CONTENT")));
        assert!(result.iter().any(|p| p.contains("test content")));
    }

    #[tokio::test]
    async fn test_fs_search_no_matches() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("test.txt"), "content")
            .await
            .unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "nonexistent".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        assert_eq!(result.len(), 1);
        assert!(result[0].contains("No matches found"));
    }

    #[tokio::test]
    async fn test_fs_search_invalid_regex() {
        let temp_dir = TempDir::new().unwrap();

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "[invalid".to_string(),
                file_pattern: None,
            })
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid regex pattern"));
    }
}
