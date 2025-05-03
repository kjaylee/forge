#![allow(dead_code)]
/// Maximum character limit for truncation
const MAX_LIMIT: usize = 40_000;

/// Result of a truncation operation
#[derive(Debug, Clone, PartialEq)]
pub struct TruncationResult {
    /// The actual content passed for truncation.
    pub actual: String,
    /// The prefix portion of the truncated content (if applicable)
    pub prefix: Option<String>,
    /// The suffix portion of the truncated content (if applicable)
    pub suffix: Option<String>,
}

impl TruncationResult {
    /// Check if this result represents truncated content
    pub fn is_truncated(&self) -> bool {
        self.prefix.is_some() || self.suffix.is_some()
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
    /// Creates a default truncator that keeps the prefix up to MAX_LIMIT characters
    fn default() -> Self {
        Self::Prefix(MAX_LIMIT)
    }
}

impl Truncator {
    /// Creates a truncator that keeps the prefix (beginning) of the content
    /// up to the specified number of characters
    pub fn from_start(prefix_chars: usize) -> Self {
        Self::Prefix(prefix_chars)
    }

    /// Creates a truncator that keeps the suffix (end) of the content
    /// up to the specified number of characters
    pub fn from_suffix(suffix_chars: usize) -> Self {
        Self::Suffix(suffix_chars)
    }

    /// Creates a truncator that keeps both the beginning and end of the content
    /// with the specified character counts for each
    pub fn from_prefix_suffix(prefix_chars: usize, suffix_chars: usize) -> Self {
        Self::PrefixSuffix(prefix_chars, suffix_chars)
    }

    /// Apply this truncation strategy to the given content
    ///
    /// # Arguments
    /// * `content` - The text content to truncate
    ///
    /// # Returns
    /// A TruncationResult containing the truncated content
    pub fn apply<T: AsRef<str>>(self, content: T) -> TruncationResult {
        let content = content.as_ref();

        // If content is empty, return as is
        if content.is_empty() {
            return TruncationResult { prefix: None, suffix: None, actual: content.to_string() };
        }

        // Get character count (not byte count)
        let char_count = content.chars().count();

        // Apply the truncation strategy
        match self {
            Truncator::Prefix(limit) => self.apply_prefix(content, char_count, limit),
            Truncator::Suffix(limit) => self.apply_suffix(content, char_count, limit),
            Truncator::PrefixSuffix(prefix_limit, suffix_limit) => {
                // TODO: why can't we use already existing methods. (apply_prefix, apply_suffix).
                self.apply_prefix_suffix(content, char_count, prefix_limit, suffix_limit)
            }
        }
    }

    /// Helper method to truncate content from the beginning
    fn apply_prefix(&self, content: &str, char_count: usize, limit: usize) -> TruncationResult {
        if char_count <= limit {
            return TruncationResult { prefix: None, suffix: None, actual: content.to_string() };
        }

        // Find the byte index corresponding to the character limit
        let truncated = content.chars().take(limit).collect::<String>();

        TruncationResult {
            prefix: Some(truncated),
            suffix: None,
            actual: content.to_string(),
        }
    }

    /// Helper method to truncate content from the end
    fn apply_suffix(&self, content: &str, char_count: usize, limit: usize) -> TruncationResult {
        if char_count <= limit {
            return TruncationResult { prefix: None, suffix: None, actual: content.to_string() };
        }

        // Skip to the start of the suffix
        let truncated = content.chars().skip(char_count - limit).collect::<String>();

        TruncationResult {
            prefix: None,
            suffix: Some(truncated),
            actual: content.to_string(),
        }
    }

    /// Helper method to truncate content from both prefix and suffix
    fn apply_prefix_suffix(
        &self,
        content: &str,
        char_count: usize,
        prefix_limit: usize,
        suffix_limit: usize,
    ) -> TruncationResult {
        // If the combined limits exceed or equal content length, return the whole content
        if prefix_limit + suffix_limit >= char_count {
            return TruncationResult { prefix: None, suffix: None, actual: content.to_string() };
        }

        // Get the prefix portion
        let prefix = content.chars().take(prefix_limit).collect::<String>();

        // Get the suffix portion
        let suffix = content
            .chars()
            .skip(char_count - suffix_limit)
            .collect::<String>();

        TruncationResult {
            prefix: Some(prefix),
            suffix: Some(suffix),
            actual: content.to_string(),
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

        let result = strategy.apply(content);

        // Should contain only the first 10 characters
        assert!(result.prefix.is_some());
        assert!(result.prefix.as_ref().unwrap().starts_with("ABCDEFGHIJ"));
        assert!(result.suffix.is_none());
    }

    #[test]
    fn test_truncate_strategy_end() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".repeat(10); // 260 chars
        let strategy = Truncator::Suffix(10);

        let result = strategy.apply(content);

        // Should contain only the last 10 characters
        assert!(result.suffix.is_some());
        assert!(result.suffix.as_ref().unwrap().contains("QRSTUVWXYZ"));
        assert!(result.prefix.is_none());
    }

    #[test]
    fn test_truncate_strategy_both() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".repeat(10); // 260 chars
        let strategy = Truncator::PrefixSuffix(10, 10);

        let result = strategy.apply(content);

        // Should contain first 10 and last 10 characters
        assert!(result.prefix.is_some());
        assert!(result.suffix.is_some());
        assert!(result.prefix.as_ref().unwrap().starts_with("ABCDEFGHIJ"));
        assert!(result.suffix.as_ref().unwrap().contains("QRSTUVWXYZ"));
    }

    #[test]
    fn test_truncate_within_limit() {
        let content = "Short content";
        let strategy = Truncator::Prefix(100);

        let result = strategy.apply(content);

        // Should return the original content as is
        assert!(result.prefix.is_none());
        assert!(result.suffix.is_none());
        assert_eq!(result.actual, content);
    }

    #[test]
    fn test_truncate_strategy_both_overlapping() {
        let content = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"; // 26 chars
        let strategy = Truncator::PrefixSuffix(15, 15);

        let result = strategy.apply(content);

        // Should return the original content as the combined limits exceed content length
        assert!(result.prefix.is_none());
        assert!(result.suffix.is_none());
        assert_eq!(result.actual, content);
    }
}
