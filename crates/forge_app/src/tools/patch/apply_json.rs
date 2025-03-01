use std::path::Path;

// No longer using dissimilar for fuzzy matching
use forge_domain::{ExecutableTool, NamedTool, ToolDescription, ToolName};
use forge_tool_macros::ToolDescription;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::fs;

use crate::tools::syn;
use crate::tools::utils::assert_absolute_path;

// Removed fuzzy matching threshold as we only use exact matching now

/// A match found in the source text. Represents a range in the source text that
/// can be used for extraction or replacement operations. Stores the position
/// and length to allow efficient substring operations.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct Range {
    /// Starting position of the match in source text
    start: usize,
    /// Length of the matched text
    length: usize,
}

impl Range {
    /// Create a new match from a start position and length
    fn new(start: usize, length: usize) -> Self {
        Self { start, length }
    }

    /// Get the end position (exclusive) of this match
    fn end(&self) -> usize {
        self.start + self.length
    }

    /// Try to find an exact match in the source text
    fn find_exact(source: &str, search: &str) -> Option<Self> {
        source
            .find(search)
            .map(|start| Self::new(start, search.len()))
    }

    // Fuzzy matching removed - we only use exact matching
}

impl From<Range> for std::ops::Range<usize> {
    fn from(m: Range) -> Self {
        m.start..m.end()
    }
}

// MatchSequence struct and implementation removed - we only use exact matching

#[derive(Debug, Error)]
enum Error {
    #[error("Failed to read/write file: {0}")]
    FileOperation(#[from] std::io::Error),
    #[error("Could not find match for search text: {0}")]
    NoMatch(String),
    #[error("Could not find swap target text: {0}")]
    NoSwapTarget(String),
}

fn apply_replacement(source: String, replacement: &Replacement) -> Result<String, Error> {
    let search = replacement.search.as_str();

    // Handle empty search string - only certain operations make sense here
    if replacement.search.is_empty() {
        return match &replacement.operation {
            // Append to the end of the file
            Operation::Append(content) => Ok(format!("{}{}", source, content)),
            // Prepend to the beginning of the file
            Operation::Prepend(content) => Ok(format!("{}{}", content, source)),
            // Replace is equivalent to completely replacing the file
            Operation::Replace(content) => Ok(content.clone()),
            // Swap doesn't make sense with empty search - keep source unchanged
            Operation::Swap(_) => Ok(source),
        };
    }

    // Find the exact match to operate on
    let patch = Range::find_exact(&source, search)
        .ok_or_else(|| Error::NoMatch(replacement.search.clone()))?;

    // Apply the operation based on its type
    match &replacement.operation {
        // Prepend content before the matched text
        Operation::Prepend(content) => Ok(format!(
            "{}{}{}",
            &source[..patch.start],
            content,
            &source[patch.start..]
        )),

        // Append content after the matched text
        Operation::Append(content) => Ok(format!(
            "{}{}{}",
            &source[..patch.end()],
            content,
            &source[patch.end()..]
        )),

        // Replace matched text with new content
        Operation::Replace(content) => Ok(format!(
            "{}{}{}",
            &source[..patch.start],
            content,
            &source[patch.end()..]
        )),

        // Swap with another text in the source
        Operation::Swap(target) => {
            // Find the target text to swap with
            let target_patch = Range::find_exact(&source, target)
                .ok_or_else(|| Error::NoSwapTarget(target.clone()))?;

            // Handle the case where patches overlap
            if (patch.start <= target_patch.start && patch.end() > target_patch.start)
                || (target_patch.start <= patch.start && target_patch.end() > patch.start)
            {
                // For overlapping ranges, we just do an ordinary replacement
                return Ok(format!(
                    "{}{}{}",
                    &source[..patch.start],
                    target,
                    &source[patch.end()..]
                ));
            }

            // We need to handle different ordering of patches
            if patch.start < target_patch.start {
                // Original text comes first
                Ok(format!(
                    "{}{}{}{}{}",
                    &source[..patch.start],
                    target,
                    &source[patch.end()..target_patch.start],
                    &source[patch.start..patch.end()],
                    &source[target_patch.end()..]
                ))
            } else {
                // Target text comes first
                Ok(format!(
                    "{}{}{}{}{}",
                    &source[..target_patch.start],
                    &source[patch.start..patch.end()],
                    &source[target_patch.end()..patch.start],
                    target,
                    &source[patch.end()..]
                ))
            }
        }
    }
}

/// Operation types that can be performed on matched text
#[derive(Deserialize, Serialize, JsonSchema, Debug, Clone, PartialEq)]
#[serde(tag = "type", content = "content")]
pub enum Operation {
    /// Prepend content before the matched text
    Prepend(String),

    /// Append content after the matched text
    Append(String),

    /// Replace the matched text with new content
    Replace(String),

    /// Swap the matched text with another text (search for the second text and
    /// swap them)
    Swap(String),
}

/// A single search and operation pair
#[derive(Deserialize, Serialize, JsonSchema, Debug, Clone)]
pub struct Replacement {
    /// The text to search for in the source. If empty, operation applies to the
    /// end of the file.
    pub search: String,

    /// The operation to perform on the matched text
    pub operation: Operation,
}

#[derive(Deserialize, JsonSchema)]
pub struct ApplyPatchJsonInput {
    pub path: String,
    pub replacement: Replacement,
}

/// Performs a single text operation (prepend, append, replace, swap, delete) on
/// matched text in a file. The operation is applied to the first match found in
/// the text.
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

/// Process the file modification and return the formatted output
async fn process_file_modifications(
    path: &Path,
    replacement: &Replacement,
) -> Result<String, Error> {
    let content = fs::read_to_string(path).await?;
    let content = apply_replacement(content, replacement)?;
    fs::write(path, &content).await?;

    let warning = syn::validate(path, &content).map(|e| e.to_string());
    Ok(format_output(
        path.to_string_lossy().as_ref(),
        &content,
        warning.as_deref(),
    ))
}

#[async_trait::async_trait]
impl ExecutableTool for ApplyPatchJson {
    type Input = ApplyPatchJsonInput;

    async fn call(&self, input: Self::Input) -> anyhow::Result<String> {
        let path = Path::new(&input.path);
        assert_absolute_path(path)?;

        Ok(process_file_modifications(path, &input.replacement).await?)
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
        replacement: Option<Replacement>,
        result: Option<String>,
    }

    impl fmt::Display for PatchTest {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let replacement = match &self.replacement {
                Some(r) => r.to_string(),
                None => String::new(),
            };
            // Use the original tag "REPLACEMENTS" for backward compatibility
            write!(
                f,
                "\n<!-- INITIAL -->{}\n<!-- REPLACEMENTS -->{}\n<!-- FINAL -->{}",
                self.initial,
                replacement,
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
                replacement: None,
                result: Default::default(),
            }
        }

        /// Replace matched text with new content
        fn replace(mut self, search: impl ToString, content: impl ToString) -> Self {
            self.replacement = Some(Replacement {
                search: search.to_string(),
                operation: Operation::Replace(content.to_string()),
            });
            self
        }

        /// Prepend content before matched text
        fn prepend(mut self, search: impl ToString, content: impl ToString) -> Self {
            self.replacement = Some(Replacement {
                search: search.to_string(),
                operation: Operation::Prepend(content.to_string()),
            });
            self
        }

        /// Append content after matched text
        fn append(mut self, search: impl ToString, content: impl ToString) -> Self {
            self.replacement = Some(Replacement {
                search: search.to_string(),
                operation: Operation::Append(content.to_string()),
            });
            self
        }

        /// Swap matched text with target text
        fn swap(mut self, search: impl ToString, target: impl ToString) -> Self {
            self.replacement = Some(Replacement {
                search: search.to_string(),
                operation: Operation::Swap(target.to_string()),
            });
            self
        }

        // TODO: tests don't need to write files to disk
        fn execute(mut self) -> Result<Self, Error> {
            if let Some(replacement) = &self.replacement {
                self.result = Some(apply_replacement(self.initial.clone(), replacement)?);
                Ok(self)
            } else {
                // No replacement specified - return original content
                self.result = Some(self.initial.clone());
                Ok(self)
            }
        }
    }

    // For backward compatibility with existing snapshots, format all operations
    // using the original SEARCH/REPLACE format where possible
    impl Display for Replacement {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match &self.operation {
                // For backward compatibility with tests, use REPLACE instead of specialized tags
                Operation::Prepend(content) => write!(
                    f,
                    "\n<!-- SEARCH -->{}\n<!-- PREPEND -->{}",
                    self.search, content
                ),
                Operation::Append(content) => write!(
                    f,
                    "\n<!-- SEARCH -->{}\n<!-- APPEND -->{}",
                    self.search, content
                ),
                Operation::Replace(content) => write!(
                    f,
                    "\n<!-- SEARCH -->{}\n<!-- REPLACE -->{}",
                    self.search, content
                ),
                // For new operations that don't have existing snapshots, use new tags
                Operation::Swap(target) => write!(
                    f,
                    "\n<!-- SEARCH -->{}\n<!-- SWAP -->{}",
                    self.search, target
                ),
            }
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
     * Single Replacement Behavior
     * Tests behavior when single replacements are performed
     */
    #[test]
    fn replaces_only_first_match() {
        let actual = PatchTest::new("foo bar foo")
            .replace("foo", "baz")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Exact Matching Behavior
     * Tests the exact matching behavior
     */

    #[test]
    fn no_match_with_hyphenated_pattern() {
        let result = PatchTest::new("abc foobar pqr")
            .replace("foo-bar", "replaced") // Should NOT match "foobar" with hyphen
            .execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find match"));
    }

    #[test]
    fn no_match_with_prefix() {
        let result = PatchTest::new("foox baz foo")
            .replace("afoo", "bar") // Should NOT match "foox" or "foo" with "a" prefix
            .execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find match"));
    }

    #[test]
    fn matches_only_first_occurrence() {
        let actual = PatchTest::new("foo foox foo")
            .replace("foo", "bar") // Should replace first exact "foo" only
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
    fn single_replacement_only() {
        let actual = PatchTest::new("outer inner outer")
            .replace("outer inner outer", "modified inner")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Complex Replacements
     * Tests complicated scenarios like nested and overlapping matches
     */

    /*
     * Operation Type Tests
     * Tests for each specific operation type
     */

    #[test]
    fn prepend_operation() {
        let actual = PatchTest::new("Hello World!")
            .prepend("Hello", "Greetings, ")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn append_operation() {
        let actual = PatchTest::new("Hello World")
            .append("World", "!")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn replace_operation() {
        let actual = PatchTest::new("Hello World")
            .replace("World", "Universe")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn swap_operation() {
        let actual = PatchTest::new("Hello World")
            .swap("Hello", "World")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn swap_with_overlap() {
        let actual = PatchTest::new("Hello World")
            .swap("Hello W", "orld")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn swap_target_not_found() {
        let result = PatchTest::new("Hello World")
            .swap("Hello", "Universe")
            .execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find swap target"));
    }

    #[test]
    fn empty_search_prepend() {
        let actual = PatchTest::new("Hello World")
            .prepend("", "Start: ")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn empty_search_append() {
        let actual = PatchTest::new("Hello World")
            .append("", " End")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn empty_search_replace() {
        let actual = PatchTest::new("Hello World")
            .replace("", "Completely New Content")
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    /*
     * Error Cases
     * Tests error handling and validation
     */

    #[test]
    fn delete_single_line_only() {
        let actual = PatchTest::new("line1\nline2\nline1\nline3")
            .replace("line1\n", "") // Using replace with empty string instead of delete for compatibility
            .execute()
            .unwrap();
        insta::assert_snapshot!(actual);
    }

    #[test]
    fn empty_search_text() {
        let actual = PatchTest::new("").replace("", "foo").execute().unwrap(); // Using replace instead of append for compatibility
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
    fn non_matching_pattern() {
        let result = PatchTest::new("fo").replace("foo", "bar").execute();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Could not find match"));
    }
}
