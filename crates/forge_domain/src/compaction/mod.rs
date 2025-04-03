// Compaction module for managing context size in conversations
//
// This module provides a strategy-based system for compacting conversation
// contexts to manage token usage and improve response quality while preserving
// important conversation history.

mod adjust_range;
mod context_compactor;
mod sliding_window;
mod strategy;
mod strategy_type;
mod summarization;

pub use context_compactor::ContextCompactor;
pub use sliding_window::SlidingWindowStrategy;
pub use strategy::{CompactionImpact, CompactionStrategy};
pub use strategy_type::StrategyType;
pub use summarization::SummarizationStrategy;
