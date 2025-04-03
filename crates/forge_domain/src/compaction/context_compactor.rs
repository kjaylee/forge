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
use crate::{impact::calculate_compaction_improvement, Agent, Context, Services};

/// Handles the compaction of conversation contexts to manage token usage
/// using a strategy-based approach for flexibility and extensibility
pub struct ContextCompactor<S> {
    strategies: Vec<StrategyType<S>>,
}

impl<S: Services> ContextCompactor<S> {
    /// Creates a new ContextCompactor instance with default strategies
    pub fn new(services: Arc<S>) -> Self {
        Self {
            strategies: vec![
                StrategyType::Summarization(SummarizationStrategy::new(Arc::clone(&services))),
                StrategyType::SlidingWindow(SlidingWindowStrategy),
            ],
        }
    }
    /// Main compaction method that checks if compaction is needed
    /// and applies the most effective strategy
    pub async fn compact_context(
        &self,
        agent: &Agent,
        context: Context,
        usage: Option<usize>,
    ) -> Result<Context> {
        if let Some(ref compact) = agent.compact {
            if !compact.should_compact(&context, usage) {
                return Ok(context);
            }

            debug!(agent_id = %agent.id, "Context compaction triggered");

            // Clone the original context for comparison later
            let original_context = context.clone();

            // Try each strategy in order until one is applicable and provides significant
            // improvement
            for strategy in &self.strategies {
                if strategy.is_applicable(compact, context.clone()) {
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        "Attempting compaction strategy"
                    );

                    let compacted = strategy.compact(compact, context.clone()).await?;

                    // Check if this strategy had significant improvement
                    let original_msg_count = original_context.messages.len();
                    let new_msg_count = compacted.messages.len();

                    let improvement =
                        calculate_compaction_improvement(&original_context, &compacted);

                    // If this strategy had significant improvement (> 20%), use its result
                    if improvement > 20.0 {
                        info!(
                            agent_id = %agent.id,
                            strategy = strategy.id(),
                            original_messages = original_msg_count,
                            new_messages = new_msg_count,
                            improvement = %format!("{:.2}%", improvement),
                            "Compaction strategy had significant impact"
                        );
                        return Ok(compacted);
                    }

                    // Otherwise, continue with the next strategy
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        improvement = %format!("{:.2}%", improvement),
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
