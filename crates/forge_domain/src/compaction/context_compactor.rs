// Context compaction implementation
//
// This file contains the ContextCompactor struct that manages
// the application of various compaction strategies to conversation contexts.

use std::sync::Arc;

use anyhow::Result;
use tracing::{debug, info};

use super::sliding_window::SlidingWindowStrategy;
use super::strategy_type::StrategyType;
use super::summarization::SummarizationStrategy;
use crate::{Agent, Context, Services};

/// Handles the compaction of conversation contexts to manage token usage
/// using a strategy-based approach for flexibility and extensibility
pub struct ContextCompactor<S> {
    strategies: Vec<StrategyType<S>>,
}

impl<S: Services> ContextCompactor<S> {
    /// Creates a new ContextCompactor instance with default strategies
    pub fn new(services: Arc<S>) -> Self {
        let mut compactor = Self { strategies: Vec::new() };

        // Register default strategies in order of preference
        compactor.register_strategy(StrategyType::Summarization(SummarizationStrategy::new(
            Arc::clone(&services),
        )));
        compactor.register_strategy(StrategyType::SlidingWindow(SlidingWindowStrategy));

        compactor
    }

    /// Registers a custom compaction strategy
    pub fn register_strategy(&mut self, strategy: StrategyType<S>) {
        self.strategies.push(strategy);
    }

    /// Main compaction method that checks if compaction is needed
    /// and applies the most effective strategy
    pub async fn compact_context(&self, agent: &Agent, context: Context) -> Result<Context> {
        if let Some(ref compact) = agent.compact {
            if !compact.should_compact(&context) {
                return Ok(context);
            }

            debug!(agent_id = %agent.id, "Context compaction triggered");

            // Try each strategy in order until one is applicable and provides significant
            // impact
            for strategy in &self.strategies {
                if strategy.is_applicable(compact, &context) {
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        "Attempting compaction strategy"
                    );

                    let (compacted, impact) = strategy.compact(compact, context.clone()).await?;

                    // If this strategy had significant impact, use its result
                    if impact.is_significant() {
                        info!(
                            agent_id = %agent.id,
                            strategy = strategy.id(),
                            original_messages = impact.original_messages,
                            new_messages = impact.new_messages,
                            "Compaction strategy had significant impact"
                        );
                        return Ok(compacted);
                    }

                    // Otherwise, continue with the next strategy
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        "Compaction strategy had insufficient impact, trying next strategy"
                    );
                }
            }

            // If no strategy had significant impact, return the original context
            debug!(agent_id = %agent.id, "No compaction strategy had significant impact");
        }

        Ok(context)
    }
}
