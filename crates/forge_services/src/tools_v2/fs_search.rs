use std::collections::HashSet;
use std::fs::File;
use std::path::Path;

use anyhow::Context;
use forge_app::{FsSearchService, Match, MatchResult, SearchResult};
use forge_walker::Walker;
use grep_searcher::sinks::UTF8;

use crate::utils::assert_absolute_path;

// Using FSSearchInput from forge_domain

// Helper to handle FSSearchInput functionality
struct FSSearchHelper<'a> {
    path: &'a str,
    regex: Option<&'a String>,
    file_pattern: Option<&'a String>,
}

impl FSSearchHelper<'_> {
    fn path(&self) -> &str {
        self.path
    }

    fn regex(&self) -> Option<&String> {
        self.regex
    }

    fn get_file_pattern(&self) -> anyhow::Result<Option<glob::Pattern>> {
        Ok(match &self.file_pattern {
            Some(pattern) => Some(
                glob::Pattern::new(pattern)
                    .with_context(|| format!("Invalid glob pattern: {pattern}"))?,
            ),
            None => None,
        })
    }

    fn match_file_path(&self, path: &Path) -> anyhow::Result<bool> {
        // Don't process directories
        if path.is_dir() {
            return Ok(false);
        }

        // If no pattern is specified, match all files
        let pattern = self.get_file_pattern()?;
        if pattern.is_none() {
            return Ok(true);
        }

        // Otherwise, check if the file matches the pattern
        Ok(path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| !name.is_empty() && pattern.unwrap().matches(name)))
    }
}

/// Recursively searches directories for files by content (regex) and/or name
/// (glob pattern). Provides context-rich results with line numbers for content
/// matches. Two modes: content search (when regex provided) or file finder
/// (when regex omitted). Uses case-insensitive Rust regex syntax. Requires
/// absolute paths. Avoids binary files and excluded directories. Best for code
/// exploration, API usage discovery, configuration settings, or finding
/// patterns across projects. For large pages, returns the first 200
/// lines and stores the complete content in a temporary file for
/// subsequent access.
#[derive(Default)]
pub struct ForgeFsSearch;

impl ForgeFsSearch {
    pub fn new() -> Self {
        Self
    }
    async fn search(
        input_path: String,
        input_regex: Option<String>,
        file_pattern: Option<String>,
    ) -> anyhow::Result<Option<SearchResult>> {
        let helper = FSSearchHelper {
            path: &input_path,
            regex: input_regex.as_ref(),
            file_pattern: file_pattern.as_ref(),
        };

        let path = Path::new(helper.path());
        assert_absolute_path(path)?;

        let regex = match helper.regex() {
            Some(regex) => {
                let pattern = format!("(?i){regex}"); // Case-insensitive by default
                Some(
                    grep_regex::RegexMatcher::new(&pattern)
                        .with_context(|| format!("Invalid regex pattern: {regex}"))?,
                )
            }
            None => None,
        };
        let paths = retrieve_file_paths(path).await?;

        let mut matches = Vec::new();

        for path in paths {
            if !helper.match_file_path(path.as_path())? {
                continue;
            }

            // File name only search mode
            if regex.is_none() {
                matches.push(Match { path: path.to_string_lossy().to_string(), result: None });
                continue;
            }

            // Process the file line by line to find content matches
            if let Some(regex) = &regex {
                let mut searcher = grep_searcher::Searcher::new();
                let path_string = path.to_string_lossy().to_string();

                let file = File::open(path)?;
                let mut found_match = false;
                searcher.search_file(
                    regex,
                    &file,
                    UTF8(|line_num, line| {
                        found_match = true;
                        // Format match in ripgrep style: filepath:line_num:content
                        matches.push(Match {
                            path: path_string.clone(),
                            result: Some(MatchResult::Found {
                                line_number: line_num as usize + 1,
                                line: line.to_string(),
                            }),
                        });

                        Ok(true)
                    }),
                )?;

                // If no matches found in content but we're looking for content,
                // don't add this file to matches
                if !found_match && helper.regex().is_some() {
                    continue;
                }
            }
        }
        if matches.is_empty() {
            return Ok(None);
        }

        Ok(Some(SearchResult { matches }))
    }
}

#[async_trait::async_trait]
impl FsSearchService for ForgeFsSearch {
    async fn search(
        &self,
        input_path: String,
        input_regex: Option<String>,
        file_pattern: Option<String>,
    ) -> anyhow::Result<Option<SearchResult>> {
        Self::search(input_path, input_regex, file_pattern).await
    }
}

async fn retrieve_file_paths(dir: &Path) -> anyhow::Result<Vec<std::path::PathBuf>> {
    if dir.is_dir() {
        // note: Paths needs mutable to avoid flaky tests.
        #[allow(unused_mut)]
        let mut paths = Walker::max_all()
            .cwd(dir.to_path_buf())
            .get()
            .await
            .with_context(|| format!("Failed to walk directory '{}'", dir.display()))?
            .into_iter()
            .map(|file| dir.join(file.path))
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();

        #[cfg(test)]
        paths.sort();

        Ok(paths)
    } else {
        Ok(Vec::from_iter([dir.to_path_buf()]))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::attachment::tests::MockInfrastructure;
    use crate::utils::TempDir;
    use pretty_assertions::assert_eq;
    use std::sync::Arc;
    use tokio::fs;

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

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("test".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains("test1.txt"));
        assert!(result.contains("test2.txt"));
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

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("test".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: Some("*.rs".to_string()),
                },
            )
            .await
            .unwrap();

        assert!(result.contains("test2.rs"));
    }

    #[tokio::test]
    async fn test_fs_search_filenames_only() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("test1.txt"), "Hello world")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("test2.txt"), "Another case")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("other.txt"), "No match here")
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: None,
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: Some("test*.txt".to_string()),
                },
            )
            .await
            .unwrap();

        assert!(result.contains("test1.txt"));
        assert!(result.contains("test2.txt"));
        assert!(!result.contains("other.txt"));
    }

    #[tokio::test]
    async fn test_fs_search_with_context() {
        let temp_dir = TempDir::new().unwrap();
        let content = "line 1\nline 2\ntest line\nline 4\nline 5";

        fs::write(temp_dir.path().join("test.txt"), content)
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("test".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains("test line"));
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
        fs::write(sub_dir.join("best.txt"), "this is proper\n test content")
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("test".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains("test1.txt"));
        assert!(result.contains("test2.txt"));
        assert!(result.contains("best.txt"));
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

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("test".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains("TEST CONTENT"));
        assert!(result.contains("test content"));
    }

    #[tokio::test]
    async fn test_fs_search_no_matches() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("test.txt"), "content")
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("nonexistent".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains("No matches found."));
    }

    #[tokio::test]
    async fn test_fs_search_list_all_files() {
        let temp_dir = TempDir::new().unwrap();

        fs::write(temp_dir.path().join("file1.txt"), "content1")
            .await
            .unwrap();
        fs::write(temp_dir.path().join("file2.rs"), "content2")
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: None,
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains("file1.txt"));
        assert!(result.contains("file2.rs"));
    }

    #[tokio::test]
    async fn test_fs_search_invalid_regex() {
        let temp_dir = TempDir::new().unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().to_string_lossy().to_string(),
                    regex: Some("[invalid".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Invalid regex pattern"));
    }

    #[tokio::test]
    async fn test_fs_search_relative_path() {
        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: "relative/path".to_string(),
                    regex: Some("test".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await;

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Path must be absolute"));
    }
    #[tokio::test]
    async fn test_format_display_path() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");

        // Create a mock infrastructure with controlled cwd
        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();

        // Test with a mock path
        let display_path = fs_search.format_display_path(Path::new(&file_path));

        // Since MockInfrastructure has a fixed cwd of "/test",
        // and our temp path won't start with that, we expect the full path
        assert!(display_path.is_ok());
        assert_eq!(display_path.unwrap(), file_path.display().to_string());
    }

    #[tokio::test]
    async fn test_fs_search_in_specific_file() {
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

        fs::write(temp_dir.path().join("best.txt"), "nice code.")
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();

        // case 1: search within a specific file
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().join("best.txt").display().to_string(),
                    regex: Some("nice".to_string()),
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();

        assert!(result.contains(&format!(
            "{}:1:nice code.",
            temp_dir.path().join("best.txt").display()
        )));

        // case 2: check if file is present or not by using search tool.
        let result = fs_search
            .call(
                &mut ToolCallContext::default(),
                FSSearchInput {
                    explanation: None,
                    path: temp_dir.path().join("best.txt").display().to_string(),
                    regex: None,
                    start_index: None,
                    max_search_lines: None,
                    file_pattern: None,
                },
            )
            .await
            .unwrap();
        assert!(result.contains(&format!("{}", temp_dir.path().join("best.txt").display())));
    }

    #[tokio::test]
    async fn test_fs_large_result() {
        let temp_dir = TempDir::new().unwrap();

        let content = (0..20)
            .map(|i| format!("line {} content", i))
            .collect::<Vec<_>>()
            .join("\n");
        fs::write(temp_dir.path().join("file1.txt"), &content)
            .await
            .unwrap();

        let infra = Arc::new(MockInfrastructure::new());
        let fs_search = ForgeFsSearch::new();
        let result = fs_search
            .search(
                temp_dir.path().to_string_lossy().to_string(),
                Some("content".into()),
                None,
            )
            .await
            .unwrap();
        assert!(result.contains("content is truncated to 10 lines"))
    }
}
