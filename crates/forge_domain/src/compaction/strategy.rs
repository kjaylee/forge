use async_trait::async_trait;

/// User-defined compaction strategy for managing context size
/// Each implementation provides a different approach to context
/// management with its own applicability criteria and compaction logic
#[async_trait]
pub trait CompactionStrategy: Send + Sync {
    /// Get the ID of this strategy for logging and debugging
    fn id(&self) -> &'static str;

    /// Check if this strategy is applicable to the given context
    /// Strategies should be selective about when they can be applied
    fn is_applicable(&self, compact: &crate::Compact, context: crate::Context) -> bool;

    /// Apply the compaction strategy to the given context
    /// Returns the compacted context
    async fn compact(
        &self,
        compact: &crate::Compact,
        context: crate::Context,
    ) -> anyhow::Result<crate::Context>;
}
