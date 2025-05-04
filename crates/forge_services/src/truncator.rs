#![allow(dead_code)]

use std::ops::Range;
/// Maximum character limit for truncation
const MAX_LIMIT: usize = 40_000;

/// Result of a truncation operation
#[derive(Debug, Clone, PartialEq)]
pub struct TruncationResult<'a> {
    /// The actual content passed for truncation.
    pub actual: &'a str,
    /// The prefix portion of the truncated content (if applicable)
    pub prefix: Option<Range<usize>>,
    /// The suffix portion of the truncated content (if applicable)
    pub suffix: Option<Range<usize>>,
}

impl TruncationResult<'_> {
    /// Check if this result represents truncated content
    pub fn is_truncated(&self) -> bool {
        self.prefix.is_some() || self.suffix.is_some()
    }

    /// Get the prefix content if it exists
    pub fn prefix_content(&self) -> Option<&str> {
        self.prefix
            .as_ref()
            .map(|range| &self.actual[range.clone()])
    }

    /// Get the suffix content if it exists
    pub fn suffix_content(&self) -> Option<&str> {
        self.suffix
            .as_ref()
            .map(|range| &self.actual[range.clone()])
    }
}

/// A strategy for truncating text content.
///
/// This enum provides different ways to truncate text while preserving
/// meaningful portions of the content based on the specific use case.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Truncator {
    /// Retains data from the beginning up to the specified character count
    Prefix(usize),

    /// Retains data from both the beginning and end of the content
    /// First parameter is the prefix character count
    /// Second parameter is the suffix character count
    PrefixSuffix(usize, usize),

    /// Retains data from the end up to the specified character count
    Suffix(usize),
}

impl Default for Truncator {
    /// Creates a default truncator that keeps the prefix up to MAX_LIMIT
    /// characters
    fn default() -> Self {
        Self::Prefix(MAX_LIMIT)
    }
}

impl Truncator {
    /// Creates a truncator that keeps the prefix (beginning) of the content
    /// up to the specified number of characters
    pub fn from_start(prefix_chars: usize) -> Truncator {
        Self::Prefix(prefix_chars)
    }

    /// Creates a truncator that keeps the suffix (end) of the content
    /// up to the specified number of characters
    pub fn from_suffix(suffix_chars: usize) -> Truncator {
        Self::Suffix(suffix_chars)
    }

    /// Creates a truncator that keeps both the beginning and end of the content
    /// with the specified character counts for each
    pub fn from_prefix_suffix(prefix_chars: usize, suffix_chars: usize) -> Truncator {
        Self::PrefixSuffix(prefix_chars, suffix_chars)
    }

    /// Apply this truncation strategy to the given content
    ///
    /// # Arguments
    /// * `content` - The text content to truncate
    ///
    /// # Returns
    /// A TruncationResult containing the truncated content
    pub fn truncate<'a>(self, content: &'a str) -> TruncationResult<'a> {

        // If content is empty, return as is
        if content.is_empty() {
            return TruncationResult { prefix: None, suffix: None, actual: content };
        }

        // Get character count (not byte count)
        let char_count = content.chars().count();

        // Apply the truncation strategy
        match self {
            Truncator::Prefix(limit) => self.apply_prefix(content, char_count, limit),
            Truncator::Suffix(limit) => self.apply_suffix(content, char_count, limit),
            Truncator::PrefixSuffix(prefix_limit, suffix_limit) => {
                self.apply_prefix_suffix(content, char_count, prefix_limit, suffix_limit)
            }
        }
    }

    /// Helper method to truncate content from the beginning
    fn apply_prefix<'a>(
        &self,
        content: &'a str,
        char_count: usize,
        limit: usize,
    ) -> TruncationResult<'a> {
        if char_count <= limit {
            return TruncationResult { prefix: None, suffix: None, actual: content };
        }

        // Find the byte index corresponding to the character limit
        let byte_idx = content
            .char_indices()
            .nth(limit)
            .map_or(content.len(), |(idx, _)| idx);

        TruncationResult { prefix: Some(0..byte_idx), suffix: None, actual: content }
    }

    /// Helper method to truncate content from the end
    fn apply_suffix<'a>(
        &self,
        content: &'a str,
        char_count: usize,
        limit: usize,
    ) -> TruncationResult<'a> {
        if char_count <= limit {
            return TruncationResult { prefix: None, suffix: None, actual: content };
        }

        // Find the byte index corresponding to where the suffix starts
        let start_idx = content
            .char_indices()
            .nth(char_count - limit)
            .map_or(0, |(idx, _)| idx);

        TruncationResult {
            prefix: None,
            suffix: Some(start_idx..content.len()),
            actual: content,
        }
    }

    /// Helper method to truncate content from both prefix and suffix
    fn apply_prefix_suffix<'a>(
        &self,
        content: &'a str,
        char_count: usize,
        prefix_limit: usize,
        suffix_limit: usize,
    ) -> TruncationResult<'a> {
        // If the combined limits exceed or equal content length, return the whole
        // content
        if prefix_limit + suffix_limit >= char_count {
            return TruncationResult { prefix: None, suffix: None, actual: content };
        }

        // Find the byte index for prefix
        let prefix_end_idx = content
            .char_indices()
            .nth(prefix_limit)
            .map_or(content.len(), |(idx, _)| idx);

        // Find the byte index for suffix
        let suffix_start_idx = content
            .char_indices()
            .nth(char_count - suffix_limit)
            .map_or(0, |(idx, _)| idx);

        TruncationResult {
            prefix: Some(0..prefix_end_idx),
            suffix: Some(suffix_start_idx..content.len()),
            actual: content,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_truncate_strategy_start() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".repeat(10); // 260 chars
        let strategy = Truncator::Prefix(10);

        let result = strategy.truncate(&content);

        // Should contain only the first 10 characters
        assert!(result.prefix.is_some());
        let range = result.prefix.unwrap();
        assert_eq!(&content[range], "ABCDEFGHIJ");
        assert!(result.suffix.is_none());
    }

    #[test]
    fn test_truncate_strategy_end() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".repeat(10); // 260 chars
        let strategy = Truncator::Suffix(10);

        let result = strategy.truncate(&content);

        // Should contain only the last 10 characters
        assert!(result.suffix.is_some());
        let range = result.suffix.unwrap();
        assert_eq!(&content[range], "QRSTUVWXYZ");
        assert!(result.prefix.is_none());
    }

    #[test]
    fn test_truncate_strategy_both() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".repeat(10); // 260 chars
        let strategy = Truncator::PrefixSuffix(10, 10);

        let result = strategy.truncate(&content);

        // Should contain first 10 and last 10 characters
        assert!(result.prefix.is_some());
        assert!(result.suffix.is_some());
        let prefix_range = result.prefix.unwrap();
        let suffix_range = result.suffix.unwrap();
        assert_eq!(&content[prefix_range], "ABCDEFGHIJ");
        assert_eq!(&content[suffix_range], "QRSTUVWXYZ");
    }

    #[test]
    fn test_truncate_within_limit() {
        let content = "Short content";
        let strategy = Truncator::Prefix(100);

        let result = strategy.truncate(&content);

        // Should return the original content as is
        assert!(result.prefix.is_none());
        assert!(result.suffix.is_none());
        assert_eq!(result.actual, content);
    }

    #[test]
    fn test_truncate_strategy_both_overlapping() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; // 26 chars
        let strategy = Truncator::PrefixSuffix(15, 15);

        let result = strategy.truncate(&content);

        // Should return the original content as the combined limits exceed content
        // length
        assert!(result.prefix.is_none());
        assert!(result.suffix.is_none());
        assert_eq!(result.actual, content);
    }
}
