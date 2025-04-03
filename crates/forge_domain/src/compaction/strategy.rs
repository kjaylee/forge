/// Defines the core strategy trait and impact measurement for compaction
/// strategies Measures the impact of a compaction operation by tracking message
/// count and token counts before and after compaction
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompactionImpact {
    /// Number of messages in the original context
    pub original_messages: usize,
    /// Number of messages after compaction
    pub new_messages: usize,
    /// Estimated token count reduction (if available)
    pub token_reduction: Option<usize>,
}

impl CompactionImpact {
    /// Creates a new CompactionImpact instance
    pub fn new(
        original_messages: usize,
        new_messages: usize,
        token_reduction: Option<usize>,
    ) -> Self {
        Self { original_messages, new_messages, token_reduction }
    }

    /// Determines if the compaction had a significant impact
    ///
    /// A compaction is considered significant if it reduced the number of
    /// messages by at least 20% (more than 20%, so exactly 20% is not
    /// significant)
    pub fn is_significant(&self) -> bool {
        // If original was empty, no impact is possible
        if self.original_messages == 0 {
            return false;
        }

        // Calculate percentage reduction in message count
        let reduction_percentage = ((self.original_messages - self.new_messages) * 100) as f64
            / self.original_messages as f64;

        // Consider significant if reduction is more than 20%
        reduction_percentage > 20.0
    }
}

/// User-defined compaction strategy for managing context size
/// Each implementation provides a different approach to context
/// management with its own applicability criteria and compaction logic
pub trait CompactionStrategy: Send + Sync {
    /// Get the ID of this strategy for logging and debugging
    fn id(&self) -> &'static str;

    /// Check if this strategy is applicable to the given context
    /// Strategies should be selective about when they can be applied
    fn is_applicable(&self, compact: &crate::Compact, context: &crate::Context) -> bool;

    /// Apply the compaction strategy to the given context
    /// Returns the compacted context and impact measurements
    fn compact(
        &self,
        compact: &crate::Compact,
        context: crate::Context,
    ) -> impl std::future::Future<Output = anyhow::Result<(crate::Context, CompactionImpact)>> + Send;
}
