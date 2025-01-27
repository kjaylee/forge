use std::path::Path;

use dissimilar::Chunk;
use forge_domain::{NamedTool, ToolCallService, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::fs;

use crate::syn;
use crate::utils::assert_absolute_path;

/// Threshold for fuzzy matching. A score above this value is considered a
/// match. The score is calculated as the ratio of matching characters to total
/// characters.
const MATCH_THRESHOLD: f64 = 0.7;

/// Represents a potential patch match in the source text
#[derive(Debug)]
struct PatchMatch {
    text: String,
    similarity: f64,
}

impl PatchMatch {
    fn new(text: String, total_len: usize) -> Self {
        Self {
            similarity: text.chars().count() as f64 / total_len as f64,
            text,
        }
    }

    fn is_good_match(&self) -> bool {
        self.similarity >= MATCH_THRESHOLD
    }
}

#[derive(Debug, Error)]
enum Error {
    #[error("Failed to read/write file: {0}")]
    FileOperation(#[from] std::io::Error),
    #[error("Could not find match for search text: {0}")]
    NoMatch(String),
}

/// Find the best matching section using fuzzy matching
fn find_best_match(content: &str, search: &str) -> Option<PatchMatch> {
    dissimilar::diff(content, search)
        .iter()
        .filter_map(|chunk| match chunk {
            Chunk::Equal(text) => Some(PatchMatch::new(text.to_string(), search.len())),
            _ => None,
        })
        .filter(PatchMatch::is_good_match)
        .max_by(|a, b| {
            a.similarity
                .partial_cmp(&b.similarity)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
}

/// Apply a single replacement to the source text
fn apply_single_replacement(source: &str, replacement: &Replacement) -> Result<String, Error> {
    if replacement.search.is_empty() {
        // Append mode - add content at the end
        return Ok(format!("{}{}", source, replacement.content));
    }

    let patch = find_best_match(source, &replacement.search)
        .ok_or_else(|| Error::NoMatch(replacement.search.clone()))?;

    Ok(if replacement.content.is_empty() {
        // Delete mode - remove the matched content
        source.replace(&patch.text, "")
    } else {
        // Replace mode - substitute matched content with new content
        source.replace(&patch.text, &replacement.content)
    })
}

/// A single search and replace operation
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
/// Matching preserves whitespace and uses a similarity score to find the best
/// match.
#[derive(ToolDescription)]
pub struct ApplyPatchV2;

impl NamedTool for ApplyPatchV2 {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_patch_v2")
    }
}

async fn apply_replacements(
    content: String,
    replacements: Vec<Replacement>,
) -> Result<String, Error> {
    replacements.iter().try_fold(content, |acc, replacement| {
        apply_single_replacement(&acc, replacement)
    })
}

/// Format the modified content as XML with optional syntax warning
fn format_output(path: &str, content: &str, warning: Option<&str>) -> String {
    if let Some(w) = warning {
        format!(
            "<file_content\n  path=\"{}\"\n  syntax_checker_warning=\"{}\">\n{}</file_content>\n",
            path, w, content
        )
    } else {
        format!(
            "<file_content path=\"{}\">\n{}\n</file_content>\n",
            path,
            content.trim_end()
        )
    }
}

/// Process the file modifications and return the formatted output
async fn process_file_modifications(
    path: &Path,
    replacements: Vec<Replacement>,
) -> Result<String, Error> {
    let content = fs::read_to_string(path).await?;
    let modified = apply_replacements(content, replacements).await?;
    fs::write(path, &modified).await?;

    let warning = syn::validate(path, &modified).map(|e| e.to_string());
    Ok(format_output(
        path.to_string_lossy().as_ref(),
        &modified,
        warning.as_deref(),
    ))
}

#[async_trait::async_trait]
impl ToolCallService for ApplyPatchV2 {
    type Input = ApplyPatchV2Input;

    async fn call(&self, input: Self::Input) -> Result<String, String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        process_file_modifications(path, input.replacements)
            .await
            .map_err(|e| e.to_string())
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
        fn new(initial: impl ToString) -> Self {
            PatchTest {
                initial: initial.to_string(),
                replacements: Default::default(),
                result: Default::default(),
            }
        }

        fn replace(mut self, search: impl ToString, replace: impl ToString) -> Self {
            self.replacements.push(Replacement::new(search, replace));
            self
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
        let actual = PatchTest::new("Hello World")
            .replace("World", "Forge")
            .execute()
            .await
            .unwrap();
        insta::assert_snapshot!(actual);
    }
}
