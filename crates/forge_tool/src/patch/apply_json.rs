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
    // For exact matches, return immediately
    if content.contains(search) {
        return Some(PatchMatch { text: search.to_string(), similarity: 1.0 });
    }

    // Otherwise use fuzzy matching
    dissimilar::diff(content, search)
        .iter()
        .filter_map(|chunk| match chunk {
            Chunk::Equal(text) => {
                // Weight longer matches higher than shorter ones
                Some(PatchMatch {
                    text: text.to_string(),
                    similarity: text.to_string().chars().count() as f64
                        / search.chars().count() as f64,
                })
            }
            _ => None,
        })
        .filter(PatchMatch::is_good_match)
        .max_by(|a, b| {
            a.similarity
                .partial_cmp(&b.similarity)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
}

fn apply_replacements(content: String, replacements: Vec<Replacement>) -> Result<String, Error> {
    // Iterate over all replacements and apply them one by one
    replacements
        .iter()
        .try_fold(content, |source, replacement| {
            if replacement.search.is_empty() {
                // Append mode - add content at the end
                Ok(format!("{}{}", source, replacement.content))
            } else {
                let patch = find_best_match(&source, &replacement.search)
                    .ok_or_else(|| Error::NoMatch(replacement.search.clone()))?;

                Ok(if replacement.content.is_empty() {
                    // Delete mode - remove the matched content
                    source.replacen(&patch.text, "", 1)
                } else {
                    // Replace mode - substitute matched content with new content
                    source.replacen(&patch.text, &replacement.content, 1)
                })
            }
        })
}

/// A single search and replace operation
#[derive(Deserialize, Serialize, JsonSchema, Debug, Clone)]
pub struct Replacement {
    pub search: String,
    pub content: String,
}

#[derive(Deserialize, JsonSchema)]
pub struct ApplyPatchJsonInput {
    pub path: String,
    pub replacements: Vec<Replacement>,
}

/// Finds and replaces all occurrences of the search text with the replacement
/// text in the file at the given path.
#[derive(ToolDescription)]
pub struct ApplyPatchJson;

impl NamedTool for ApplyPatchJson {
    fn tool_name() -> ToolName {
        ToolName::new("tool_forge_patch_v2")
    }
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
    let content = apply_replacements(content, replacements)?;
    fs::write(path, &content).await?;

    let warning = syn::validate(path, &content).map(|e| e.to_string());
    Ok(format_output(
        path.to_string_lossy().as_ref(),
        &content,
        warning.as_deref(),
    ))
}

#[async_trait::async_trait]
impl ToolCallService for ApplyPatchJson {
    type Input = ApplyPatchJsonInput;

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

        // TODO: tests don't need to write files to disk
        fn execute(mut self) -> Result<Self, Error> {
            self.result = Some(apply_replacements(
                self.initial.clone(),
                self.replacements.clone(),
            )?);

            Ok(self)
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

    /*
     * Basic Operations
     * Tests basic functionality like exact matches, empty inputs, and simple
     * cases
     */
    #[test]
    fn exact_match_single_word() {
        let actual = PatchTest::new("Hello World")
            .replace("World", "Forge")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn fuzzy_match_with_extra_characters() {
        let actual = PatchTest::new("fooo bar")
            .replace("foo", "baz") // Should match despite extra 'o'
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn append_empty_search() {
        let actual = PatchTest::new("foo").replace("", " bar").execute().unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn delete_empty_replace() {
        let actual = PatchTest::new("foo bar baz")
            .replace("bar ", "")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Multiple Replacements
     * Tests behavior when multiple replacements are performed
     */
    #[test]
    fn different_replacements_in_sequence() {
        let actual = PatchTest::new("foo bar")
            .replace("foo", "baz")
            .replace("bar", "qux")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn replaces_only_first_match() {
        let actual = PatchTest::new("foo bar foo")
            .replace("foo", "baz")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn sequential_replacements_on_identical_text() {
        let actual = PatchTest::new("same same same")
            .replace("same", "different") // First occurrence
            .replace("same", "changed") // Second occurrence
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn sequential_non_overlapping_replacements() {
        let actual = PatchTest::new("abcdef")
            .replace("abc", "123")
            .replace("def", "456")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Fuzzy Matching Behavior
     * Tests the fuzzy matching algorithm and similarity thresholds
     */
    #[test]
    fn exact_threshold_match() {
        let actual = PatchTest::new("foox") // 3/4 = 0.75, just above MATCH_THRESHOLD
            .replace("foo", "bar")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn just_below_threshold() {
        let result = PatchTest::new("fox") // 2/3 ≈ 0.67, just below MATCH_THRESHOLD
            .replace("foo", "bar")
            .execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find match"));
    }

    #[test]
    fn fuzzy_match_with_prefix() {
        let actual = PatchTest::new("foox baz foo")
            .replace("afoo", "bar") // Should match "foox" despite "a" prefix
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn prefers_exact_matches_over_fuzzy() {
        let actual = PatchTest::new("foo foox foo")
            .replace("foo", "bar") // Should replace exact "foo" first
            .replace("foo", "baz") // Should replace second exact "foo"
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Unicode and Special Characters
     * Tests handling of non-ASCII text and special characters
     */
    #[test]
    fn unicode_characters() {
        let actual = PatchTest::new("Hello 世界")
            .replace("世界", "🌍")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn emoji_replacement() {
        let actual = PatchTest::new("Hi 👋, how are you?")
            .replace("👋", "👍")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn mixed_unicode_ascii() {
        let actual = PatchTest::new("Hello 世界 World")
            .replace("世界 World", "地球")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Whitespace Handling
     * Tests preservation of whitespace, indentation, and line endings
     */
    #[test]
    fn preserve_indentation() {
        let actual = PatchTest::new("    indented\n        more indented")
            .replace("indented", "text")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn tab_characters() {
        let actual = PatchTest::new("no_tab\thas_tab")
            .replace("has_tab", "replaced")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn multiple_line_endings() {
        let actual = PatchTest::new("line1\nline2\rline3\r\nline4")
            .replace("line2", "replaced")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Error Cases
     * Tests error handling and edge cases
     */
    #[test]
    fn nested_replacements() {
        let actual = PatchTest::new("outer inner outer")
            .replace("outer inner outer", "modified inner")
            .replace("inner", "content")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn overlapping_matches() {
        let actual = PatchTest::new("abcabcabc")
            .replace("abca", "1234")
            .replace("cabc", "5678")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Complex Replacements
     * Tests complicated scenarios like nested and overlapping matches
     */

    /*
     * Error Cases
     * Tests error handling and validation
     */

    #[test]
    fn delete_single_line_only() {
        let actual = PatchTest::new("line1\nline2\nline1\nline3")
            .replace("line1\n", "") // Delete first occurrence of line1 and its newline
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn empty_search_text() {
        let actual = PatchTest::new("").replace("", "foo").execute().unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn no_match_found() {
        let result = PatchTest::new("foo").replace("bar", "baz").execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find match"));
    }

    #[test]
    fn fuzzy_match_below_threshold() {
        let result = PatchTest::new("fo").replace("foo", "bar").execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find match"));
    }
}
