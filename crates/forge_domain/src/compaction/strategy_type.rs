// Strategy type for compaction system
//
// This file defines the enum of available compaction strategies
// and implements methods for accessing and applying them.

use anyhow::Result;

use super::sliding_window::SlidingWindowStrategy;
use super::strategy::{CompactionImpact, CompactionStrategy};
use super::summarization::SummarizationStrategy;
use crate::{Context, Services};

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
    pub fn is_applicable(&self, compact: &crate::Compact, context: &Context) -> bool {
        match self {
            StrategyType::Summarization(s) => s.is_applicable(compact, context),
            StrategyType::SlidingWindow(s) => s.is_applicable(compact, context),
        }
    }

    /// Apply the compaction strategy
    pub async fn compact(
        &self,
        compact: &crate::Compact,
        context: Context,
    ) -> Result<(Context, CompactionImpact)> {
        match self {
            StrategyType::Summarization(s) => s.compact(compact, context).await,
            StrategyType::SlidingWindow(s) => s.compact(compact, context).await,
        }
    }
}
