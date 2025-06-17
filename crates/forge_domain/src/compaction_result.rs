use serde::{Deserialize, Serialize};

/// Contains metrics related to context compaction
/// This struct provides information about the compaction operation
/// such as the original and compacted token counts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactionResult {
    /// Number of tokens in the original context
    pub original_tokens: u64,
    /// Number of tokens after compaction
    pub compacted_tokens: u64,
    /// Number of messages in the original context
    pub original_messages: u64,
    /// Number of messages after compaction
    pub compacted_messages: u64,
}

impl CompactionResult {
    /// Create a new CompactionResult with the specified metrics
    pub fn new(
        original_tokens: u64,
        compacted_tokens: u64,
        original_messages: u64,
        compacted_messages: u64,
    ) -> Self {
        Self {
            original_tokens,
            compacted_tokens,
            original_messages,
            compacted_messages,
        }
    }

    /// Calculate the percentage reduction in tokens
    pub fn token_reduction_percentage(&self) -> f64 {
        if self.original_tokens == 0 {
            return 0.0;
        }
        ((self.original_tokens - self.compacted_tokens) as f64 / self.original_tokens as f64)
            * 100.0
    }

    /// Calculate the percentage reduction in messages
    pub fn message_reduction_percentage(&self) -> f64 {
        if self.original_messages == 0 {
            return 0.0;
        }
        ((self.original_messages - self.compacted_messages) as f64 / self.original_messages as f64)
            * 100.0
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn test_token_reduction_percentage() {
        let result = CompactionResult::new(1000, 500, 20, 10);
        assert_eq!(result.token_reduction_percentage(), 50.0);

        // Edge case: no original tokens
        let result = CompactionResult::new(0, 0, 20, 10);
        assert_eq!(result.token_reduction_percentage(), 0.0);
    }

    #[test]
    fn test_message_reduction_percentage() {
        let result = CompactionResult::new(1000, 500, 20, 10);
        assert_eq!(result.message_reduction_percentage(), 50.0);

        // Edge case: no original messages
        let result = CompactionResult::new(1000, 500, 0, 0);
        assert_eq!(result.message_reduction_percentage(), 0.0);
    }
}
