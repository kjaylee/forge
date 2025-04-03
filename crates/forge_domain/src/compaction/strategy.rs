use anyhow::Result;
use async_trait::async_trait;

use super::sliding_window::SlidingWindowStrategy;
use super::summarization::SummarizationStrategy;
use crate::{Context, Services};

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


/// The available compaction strategies
pub enum StrategyType<S> {
    Summarization(SummarizationStrategy<S>),
    SlidingWindow(SlidingWindowStrategy),
}

impl<S: Services> StrategyType<S> {
    /// Get the ID of the strategy
    pub fn id(&self) -> &'static str {
        match self {
            StrategyType::Summarization(s) => s.id(),
            StrategyType::SlidingWindow(s) => s.id(),
        }
    }

    /// Check if this strategy is applicable to the given context
    pub fn is_applicable(&self, compact: &crate::Compact, context: Context) -> bool {
        match self {
            StrategyType::Summarization(s) => s.is_applicable(compact, context),
            StrategyType::SlidingWindow(s) => s.is_applicable(compact, context),
        }
    }

    /// Apply the compaction strategy
    pub async fn compact(&self, compact: &crate::Compact, context: Context) -> Result<Context> {
        match self {
            StrategyType::Summarization(s) => s.compact(compact, context).await,
            StrategyType::SlidingWindow(s) => s.compact(compact, context).await,
        }
    }
}
