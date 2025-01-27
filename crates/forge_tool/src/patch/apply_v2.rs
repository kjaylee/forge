use std::path::{Path, PathBuf};

use dissimilar::Chunk;
use forge_domain::{NamedTool, ToolCallService, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::fs;

use crate::syn;
use crate::utils::assert_absolute_path;

const MATCH_THRESHOLD: f64 = 0.7;

// The core matching function
fn find_best_match(content: &str, search: &str) -> Option<(usize, usize)> {
    // Try exact match first
    if let Some(idx) = content.find(search) {
        return Some((idx, idx + search.len()));
    }

    // Get line-by-line chunks
    let content_lines: Vec<&str> = content.lines().collect();
    let search_lines: Vec<&str> = search.lines().collect();

    'outer: for start_idx in 0..content_lines.len() {
        if start_idx + search_lines.len() > content_lines.len() {
            break;
        }

        let mut total_score = 0.0;
        for (i, search_line) in search_lines.iter().enumerate() {
            let content_line = content_lines[start_idx + i];
            let line_score = similarity_score(content_line.trim(), search_line.trim());
            total_score += line_score;

            // Early exit if line score is too low
            if line_score < MATCH_THRESHOLD * 0.5 {
                continue 'outer;
            }
        }

        let avg_score = total_score / search_lines.len() as f64;
        if avg_score >= MATCH_THRESHOLD {
            // Find the position in original content
            let mut pos = 0;
            for i in 0..start_idx {
                pos += content_lines[i].len() + 1; // +1 for newline
            }

            // Calculate the length of matched region
            let mut match_len = 0;
            for i in 0..search_lines.len() {
                match_len += content_lines[start_idx + i].len() + 1;
            }
            match_len -= 1; // Remove extra newline from last line

            return Some((pos, pos + match_len));
        }
    }

    None
}

// Apply a single replacement
fn apply_replacement(content: &str, replacement: &Replacement) -> Option<String> {
    if replacement.search.is_empty() {
        let mut result = content.to_string();
        result.push_str(&replacement.content);
        return Some(result);
    }

    if let Some((start, end)) = find_best_match(content, &replacement.search) {
        let mut result = content.to_string();
        result.replace_range(start..end, &replacement.content);
        Some(result)
    } else {
        None
    }
}

#[derive(Debug, Error)]
enum Error {
    #[error("File not found at path: {0}")]
    FileNotFound(PathBuf),
    #[error("File operation failed: {0}")]
    FileOperation(#[from] std::io::Error),
    #[error("Invalid replacement: {0}")]
    InvalidReplacement(String),
}

#[derive(Deserialize, Serialize, JsonSchema, Debug, Clone)]
pub struct Replacement {
    pub search: String,
    pub content: String,
}

#[derive(Deserialize, JsonSchema)]
pub struct ApplyPatchV2Input {
    pub path: String,
    pub replacements: Vec<Replacement>,
}

/// Replace sections in a file using JSON-based search/replace definitions.
/// Each replacement can use fuzzy matching if exact matches aren't found.
/// Matching preserves whitespace and uses a fuzzy matching algorithm when exact
/// matches fail.
#[derive(ToolDescription)]
pub struct ApplyPatchV2;

impl NamedTool for ApplyPatchV2 {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_patch_v2")
    }
}

fn similarity_score(text1: &str, text2: &str) -> f64 {
    let chunks = dissimilar::diff(text1, text2);
    let mut equal_chars = 0;
    let total_chars = text2.chars().count();

    for chunk in chunks {
        if let Chunk::Equal(text) = chunk {
            equal_chars += text.chars().count();
        }
    }

    equal_chars as f64 / total_chars as f64
}

async fn apply_replacements(
    content: String,
    replacements: Vec<Replacement>,
) -> Result<String, Error> {
    let mut result = content;

    for replacement in replacements {
        result = apply_replacement(&result, &replacement).ok_or_else(|| {
            Error::InvalidReplacement(format!(
                "Could not find match for search text: {}",
                replacement.search
            ))
        })?;
    }

    Ok(result)
}

#[async_trait::async_trait]
impl ToolCallService for ApplyPatchV2 {
    type Input = ApplyPatchV2Input;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        if !path.exists() {
            return Err(Error::FileNotFound(path.to_path_buf()).to_string());
        }

        let result: Result<_, Error> = async {
            let content = fs::read_to_string(&input.path)
                .await
                .map_err(Error::FileOperation)?;

            let modified = apply_replacements(content, input.replacements).await?;

            fs::write(&input.path, &modified)
                .await
                .map_err(Error::FileOperation)?;

            let syntax_warning = syn::validate(&input.path, &modified);

            let output = if let Some(warning) = syntax_warning {
                format!(
                    "<file_content\n  path=\"{}\"\n  syntax_checker_warning=\"{}\">\n{}</file_content>\n",
                    input.path, warning, modified
                )
            } else {
                format!(
                    "<file_content path=\"{}\">\n{}\n</file_content>\n",
                    input.path,
                    modified.trim_end()
                )
            };

            Ok(output)
        }
        .await;

        result.map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod test {
    use std::fmt::{self, Display};

    use super::*;
    use crate::utils::TempDir;

    // Test helpers
    #[derive(Debug)]
    struct PatchTest {
        initial: String,
        replacements: Vec<Replacement>,
        result: Option<String>,
    }

    impl fmt::Display for PatchTest {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let replacements = self
                .replacements
                .iter()
                .map(|a| a.to_string())
                .fold("".to_string(), |a, b| format!("{a}{b}"));
            write!(
                f,
                "\n<!-- INITIAL -->{}\n<!-- REPLACEMENTS -->{}\n<!-- FINAL -->{}",
                self.initial,
                replacements,
                self.result
                    .as_ref()
                    .expect("Test must be executed before display")
            )
        }
    }

    impl PatchTest {
        fn new(initial: impl ToString, replacements: &[Replacement]) -> Self {
            PatchTest {
                initial: initial.to_string(),
                replacements: replacements.to_vec(),
                result: None,
            }
        }

        async fn execute(mut self) -> Result<Self, String> {
            let temp_dir = TempDir::new().unwrap();
            let path = temp_dir.path().join("test.txt");
            fs::write(&path, &self.initial).await.unwrap();

            match ApplyPatchV2
                .call(ApplyPatchV2Input {
                    path: path.to_string_lossy().to_string(),
                    replacements: self.replacements.clone(),
                })
                .await
            {
                Ok(_) => {
                    let final_content = fs::read_to_string(&path).await.unwrap();
                    self.result = Some(final_content);
                    Ok(self)
                }
                Err(e) => Err(e),
            }
        }
    }

    impl Display for Replacement {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "\n<!-- SEARCH -->{}\n<!-- REPLACE -->{}",
                self.search, self.content
            )
        }
    }

    impl Replacement {
        fn new(search: impl ToString, replace: impl ToString) -> Self {
            Replacement { search: search.to_string(), content: replace.to_string() }
        }
    }

    #[tokio::test]
    async fn simple_replacement() {
        let actual = PatchTest::new("Hello World", &[Replacement::new("World", "Forge")])
            .execute()
            .await
            .unwrap();
        insta::assert_snapshot!(actual);
    }
}
