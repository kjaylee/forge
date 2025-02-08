use std::collections::HashSet;
use std::path::Path;

use console::style;
use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use forge_walker::Walker;
use regex::Regex;
use schemars::JsonSchema;
use serde::Deserialize;

use crate::utils::assert_absolute_path;

#[derive(Deserialize, JsonSchema)]
pub struct FSSearchInput {
    /// The path of the directory to search in (absolute path required). This
    /// directory will be recursively searched.
    pub path: String,
    /// The regular expression pattern to search for. Uses Rust regex syntax.
    pub regex: String,
    /// Glob pattern to filter files (e.g., '*.ts' for TypeScript files). If not
    /// provided, it will search all files (*).
    pub file_pattern: Option<String>,
}

/// Request to perform a regex search on the content across files in a specified
/// directory, providing context-rich results. This tool searches for patterns
/// or specific content across multiple files, displaying each match with
/// encapsulating context. The path must be absolute.
#[derive(ToolDescription)]
pub struct FSSearch;

impl NamedTool for FSSearch {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_fs_search")
    }
}

#[async_trait::async_trait]
impl ExecutableTool for FSSearch {
    type Input = FSSearchInput;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        let dir = Path::new(&input.path);
        assert_absolute_path(dir)?;

        if !dir.exists() {
            return Err(format!("Directory '{}' does not exist", input.path));
        }

        // Create regex pattern - case-insensitive by default
        let pattern = format!("(?i){}", input.regex);
        let regex = Regex::new(&pattern).map_err(|e| format!("Invalid regex pattern: {}", e))?;

        // TODO: Current implementation is extremely slow and inefficient.
        // It should ideally be taking in a stream of files and processing them
        // concurrently.
        let walker = Walker::max_all().cwd(dir.to_path_buf());

        let files = walker
            .get()
            .await
            .map_err(|e| format!("Failed to walk directory '{}': {}", dir.display(), e))?;

        let mut matches = Vec::new();
        let mut seen_paths = HashSet::new();

        for file in files {
            if file.is_dir() {
                continue;
            }

            let path = Path::new(&file.path);
            let full_path = dir.join(path);

            // Apply file pattern filter if provided
            if let Some(ref pattern) = input.file_pattern {
                let glob = glob::Pattern::new(pattern).map_err(|e| {
                    format!(
                        "Invalid glob pattern '{}' for file '{}': {}",
                        pattern,
                        full_path.display(),
                        e
                    )
                })?;
                if let Some(filename) = path.file_name().unwrap_or(path.as_os_str()).to_str() {
                    if !glob.matches(filename) {
                        continue;
                    }
                }
            }

            // Skip if we've already processed this file
            if !seen_paths.insert(full_path.clone()) {
                continue;
            }

            // Try to read the file content
            let content = match tokio::fs::read_to_string(&full_path).await {
                Ok(content) => content,
                Err(e) => {
                    // Skip binary or unreadable files silently
                    if e.kind() != std::io::ErrorKind::InvalidData {
                        matches.push(format!("Error reading {:?}: {}", full_path.display(), e));
                    }
                    continue;
                }
            };

            // Process the file line by line
            for (line_num, line) in content.lines().enumerate() {
                if regex.is_match(line) {
                    // Format match in ripgrep style: filepath:line_num:content
                    matches.push(format!("{}:{}:{}", full_path.display(), line_num + 1, line));
                }
            }
        }

        if matches.is_empty() {
            let output = format!(
                "{} No matches found for pattern '{}' in path '{}'",
                style("Note:").blue().bold(),
                style(&input.regex).yellow(),
                style(&input.path).cyan()
            );
            println!("{}", output);
            Ok(strip_ansi_escapes::strip_str(output))
        } else {
            println!(
                "{}\n{}",
                style("Matches:").dim(),
                RipGrepFormatter(matches.clone()).format(&regex)
            );
            Ok(matches.join("\n"))
        }
    }
}

/// RipGrepFormatter responsible for formatting search results in ripgrep format.
struct RipGrepFormatter(Vec<String>);

impl RipGrepFormatter {
    // Color format:
    // - File path in green
    // - Line number in purple
    // - Separators in gray
    // - Matching text in red & bold
    fn colorize(mut self, regex: &Regex) -> Self {
        let mut colorized = Vec::with_capacity(self.0.len());
        let separator = style(":").dim();

        for line in self.0 {
            // since we get the matches separated by ':', we can split the line to get the parts.
            let mut parts = line.splitn(3, ':');
            let (path, line_num, content) = match (parts.next(), parts.next(), parts.next()) {
                (Some(p), Some(l), Some(c)) => (p, l, c),
                _ => {
                    // Skip malformed lines
                    continue;
                }
            };

            let colored_path = style(path).green();
            let colored_line_num = style(line_num).magenta();

            // Color the content matches in red & bold
            let mut colored_content = content.to_string();
            if let Some(mat) = regex.find(content) {
                let before = &content[..mat.start()];
                let matched = style(&content[mat.start()..mat.end()]).red().bold();
                let after = &content[mat.end()..];
                colored_content = format!("{}{}{}", before, matched, after);
            }

            // Combine all parts
            let colorized_line = format!(
                "{}{}{}{}{}",
                colored_path, separator, colored_line_num, separator, colored_content
            );
            colorized.push(colorized_line);
        }

        self.0 = colorized;
        self
    }

    /// Format search results in ripgrep-like output format, grouping results by
    /// file path. Each file path is followed by its matching lines.
    fn format(mut self, regex: &Regex) -> String {
        // apply colorization as per the ripgrep formatter.
        self = self.colorize(regex);

        let mut output = String::with_capacity(self.0.len() * 64);
        let mut lines = self.0.into_iter().peekable();

        while let Some(line) = lines.next() {
            if let Some((file_path, content)) = line.split_once(':') {
                output.push_str(file_path);
                output.push('\n');
                output.push_str(content);

                while let Some(next_line) = lines.peek() {
                    if let Some((next_path, next_content)) = next_line.split_once(':') {
                        if next_path != file_path {
                            break;
                        }
                        output.push('\n');
                        output.push_str(next_content);
                        lines.next(); // Consume the peeked line
                    } else {
                        lines.next(); // Skip malformed line
                    }
                }
                output.push_str("\n\n");
            }
        }

        output
    }
}

#[cfg(test)]
mod test {
    use pretty_assertions::assert_eq;
    use tokio::fs;

    use super::*;
    use crate::utils::TempDir;

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

        let lines: Vec<_> = result.lines().collect();
        assert_eq!(lines.len(), 2);
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

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: Some("*.rs".to_string()),
            })
            .await
            .unwrap();

        let lines: Vec<_> = result.lines().collect();
        assert_eq!(lines.len(), 1);
        assert!(result.contains("test2.rs"));
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

        let lines: Vec<_> = result.lines().collect();
        assert_eq!(lines.len(), 1);
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

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        let lines: Vec<_> = result.lines().collect();
        assert_eq!(lines.len(), 3);
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

        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: temp_dir.path().to_string_lossy().to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await
            .unwrap();

        let lines: Vec<_> = result.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(result.contains("TEST CONTENT"));
        assert!(result.contains("test content"));
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

        assert!(result.contains("No matches found"));
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

    #[tokio::test]
    async fn test_fs_search_relative_path() {
        let fs_search = FSSearch;
        let result = fs_search
            .call(FSSearchInput {
                path: "relative/path".to_string(),
                regex: "test".to_string(),
                file_pattern: None,
            })
            .await;

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Path must be absolute"));
    }

    #[cfg(test)]
    mod rip_grep_formatter_tests {
        use pretty_assertions::assert_eq;
        use regex::Regex;

        use crate::fs::fs_find::RipGrepFormatter;

        #[test]
        fn test_ripgrep_formatter_single_file() {
            let input = vec!["file.txt:1:first match", "file.txt:2:second match"]
                .into_iter()
                .map(String::from)
                .collect();

            let formatter = RipGrepFormatter(input);
            let result = formatter.format(&Regex::new("match").unwrap());
            let actual = strip_ansi_escapes::strip_str(&result);
            let expected = "file.txt\n1:first match\n2:second match\n\n";
            assert_eq!(actual, expected);
        }

        #[test]
        fn test_ripgrep_formatter_multiple_files() {
            let input = vec![
                "file1.txt:1:match in file1",
                "file2.txt:1:first match in file2",
                "file2.txt:2:second match in file2",
                "file3.txt:1:match in file3",
            ]
            .into_iter()
            .map(String::from)
            .collect();

            let formatter = RipGrepFormatter(input);
            let result = formatter.format(&Regex::new("file").unwrap());
            let actual = strip_ansi_escapes::strip_str(&result);

            let expected = "file1.txt\n1:match in file1\n\nfile2.txt\n1:first match in file2\n2:second match in file2\n\nfile3.txt\n1:match in file3\n\n";
            assert_eq!(actual, expected);
        }

        #[test]
        fn test_ripgrep_formatter_empty_input() {
            let formatter = RipGrepFormatter(vec![]);
            let result = formatter.format(&Regex::new("file").unwrap());
            assert_eq!(result, "");
        }

        #[test]
        fn test_ripgrep_formatter_malformed_input() {
            let input = vec![
                "file.txt:1:valid match",
                "malformed line without separator",
                "file.txt:2:another valid match",
            ]
            .into_iter()
            .map(String::from)
            .collect();

            let formatter = RipGrepFormatter(input);
            let result = formatter.format(&Regex::new("match").unwrap());
            let actual = strip_ansi_escapes::strip_str(&result);

            let expected = "file.txt\n1:valid match\n2:another valid match\n\n";
            assert_eq!(actual, expected);
        }

        #[test]
        fn test_ripgrep_formatter_colorize() {
            let input = vec![
                "file.txt:1:test match test",
                "malformed line",
                "file.txt:2:another test",
            ]
            .into_iter()
            .map(String::from)
            .collect();

            let regex = Regex::new(r"test").unwrap();
            let formatter = RipGrepFormatter(input);
            let result = formatter
                .colorize(&regex)
                .format(&Regex::new("test").unwrap());
            let actual = strip_ansi_escapes::strip_str(&result);

            // Note: actual color codes will be stripped in the format() output
            let expected = "file.txt\n1:test match test\n2:another test\n\n";
            assert_eq!(actual, expected);
        }
    }
}
