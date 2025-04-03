// Compaction module for managing context size in conversations
//
// This module provides a strategy-based system for compacting conversation
// contexts to manage token usage and improve response quality while preserving
// important conversation history.

mod sliding_window;
mod strategy;
mod summarization;

use std::cmp::min;
use std::sync::Arc;

use anyhow::Result;
pub use sliding_window::SlidingWindowStrategy;
pub use strategy::{CompactionImpact, CompactionStrategy};
pub use summarization::SummarizationStrategy;
use tracing::{debug, info};

use crate::{Agent, Context, Role, Services};

/// The available compaction strategies
pub enum StrategyType {
    Summarization(SummarizationStrategy),
    SlidingWindow(SlidingWindowStrategy),
}

impl StrategyType {
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
    pub async fn compact<S: Services>(
        &self,
        compact: &crate::Compact,
        context: Context,
        services: &S,
    ) -> Result<(Context, CompactionImpact)> {
        match self {
            StrategyType::Summarization(s) => s.compact(compact, context, services).await,
            StrategyType::SlidingWindow(s) => s.compact(compact, context, services).await,
        }
    }
}

/// Handles the compaction of conversation contexts to manage token usage
/// using a strategy-based approach for flexibility and extensibility
pub struct ContextCompactor<S> {
    services: Arc<S>,
    strategies: Vec<StrategyType>,
}

impl<S: Services> ContextCompactor<S> {
    /// Creates a new ContextCompactor instance with default strategies
    pub fn new(services: Arc<S>) -> Self {
        let mut compactor = Self { services, strategies: Vec::new() };

        // Register default strategies in order of preference
        compactor.register_strategy(StrategyType::Summarization(SummarizationStrategy));
        compactor.register_strategy(StrategyType::SlidingWindow(SlidingWindowStrategy));

        compactor
    }

    /// Registers a custom compaction strategy
    pub fn register_strategy(&mut self, strategy: StrategyType) {
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
            let services_ref = self.services.as_ref();
            for strategy in &self.strategies {
                if strategy.is_applicable(compact, &context) {
                    debug!(
                        agent_id = %agent.id,
                        strategy = strategy.id(),
                        "Attempting compaction strategy"
                    );

                    let (compacted, impact) = strategy
                        .compact(compact, context.clone(), services_ref)
                        .await?;

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

/// Adjusts a proposed range to ensure tool call chains are preserved
///
/// This prevents compaction from breaking up related tool calls and responses
/// which could cause context loss for the agent.
pub fn adjust_range_for_tool_calls(
    context: &Context,
    start_idx: usize,
    end_idx: usize,
) -> (usize, usize) {
    let messages = &context.messages;

    // Adjust start index to include complete tool call chains
    let mut adjusted_start_idx = start_idx;
    while adjusted_start_idx > 0 {
        let prev_msg = messages.get(adjusted_start_idx - 1);
        let curr_msg = messages.get(adjusted_start_idx);

        match (prev_msg, curr_msg) {
            // If previous message has a tool call and current is user,
            // it's likely a tool call chain we should preserve
            (Some(prev), Some(curr)) if prev.has_tool_call() && curr.has_role(Role::User) => {
                adjusted_start_idx -= 1;
            }
            // Otherwise we can break here
            _ => break,
        }
    }

    // Adjust end index if needed to include any tool call at the boundary
    let mut adjusted_end_idx = end_idx;
    if let Some(msg) = messages.get(adjusted_end_idx) {
        if msg.has_tool_call() {
            // If end message has a tool call, include the next message if it's a user
            // response
            if let Some(next_msg) = messages.get(adjusted_end_idx + 1) {
                if next_msg.has_role(Role::User) {
                    adjusted_end_idx += 1;
                }
            }
        }
    }

    (adjusted_start_idx, adjusted_end_idx)
}

/// Finds all valid compressible sequences in the context, respecting the
/// preservation window
///
/// This function identifies sequences of assistant messages between user
/// messages that can be compressed by summarization, while respecting the
/// preservation window.
pub fn find_sequence(context: &Context, preserve_last_n: usize) -> Option<(usize, usize)> {
    let messages = &context.messages;
    if messages.is_empty() {
        return None;
    }

    // len will be always > 0
    let length = messages.len();
    let mut max_len = length - min(length, preserve_last_n);

    if max_len == 0 {
        return None;
    }

    // Additional check: if max_len < 1, we can't safely do max_len - 1
    if max_len < 1 {
        return None;
    }
    if messages
        .get(max_len - 1)
        .is_some_and(|msg| msg.has_tool_call())
    {
        max_len -= 1;
    }

    let user_messages = messages
        .iter()
        .enumerate()
        .take(max_len)
        .filter(|(_, message)| message.has_role(Role::User))
        .collect::<Vec<_>>();

    // If there are no user messages, there can't be any sequences
    if user_messages.is_empty() {
        return None;
    }
    let start_positions = user_messages
        .iter()
        .map(|(start, _)| min(start.saturating_add(1), max_len.saturating_sub(1)))
        .collect::<Vec<_>>();

    let mut end_positions = user_messages
        .iter()
        .skip(1)
        .map(|(pos, _)| pos.saturating_sub(1))
        .collect::<Vec<_>>();
    end_positions.push(max_len - 1);

    // If either vector is empty, there can't be any compressible sequences
    if start_positions.is_empty() || end_positions.is_empty() {
        return None;
    }

    // Find a valid sequence and adjust it to preserve tool call chains
    let range = start_positions
        .iter()
        .zip(end_positions.iter())
        .find(|(start, end)| *end > *start)
        .map(|(a, b)| (*a, *b));

    // If we found a range, adjust it to respect tool call chains
    if let Some((start, end)) = range {
        let (adjusted_start, adjusted_end) = adjust_range_for_tool_calls(context, start, end);
        return Some((adjusted_start, adjusted_end));
    }

    None
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::CompactionImpact;

    #[test]
    fn test_compaction_impact_significance() {
        // A reduction of 20% or more is significant
        let fixture = CompactionImpact::new(10, 8, Some(100));
        let actual = fixture.is_significant();
        let expected = false; // 20% reduction would be 8 messages, this is exactly 20%
        assert_eq!(actual, expected);

        let fixture = CompactionImpact::new(10, 7, Some(100));
        let actual = fixture.is_significant();
        let expected = true; // 30% reduction, which is significant
        assert_eq!(actual, expected);

        // Edge case - empty context
        let fixture = CompactionImpact::new(0, 0, Some(0));
        let actual = fixture.is_significant();
        let expected = false;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_adjust_range_for_tool_calls() {
        use crate::{ContextMessage, ToolCallFull, ToolCallId, ToolName};

        // Create a test context with tool calls
        let mut context = Context::default();

        // Add messages that form a tool call chain
        context
            .messages
            .push(ContextMessage::user("Initial message"));

        let tool_call = vec![ToolCallFull {
            name: ToolName::new("test_tool"),
            call_id: Some(ToolCallId::new("1")),
            arguments: serde_json::json!({"arg": "value"}),
        }];

        context
            .messages
            .push(ContextMessage::assistant("Using a tool", Some(tool_call)));
        context
            .messages
            .push(ContextMessage::user("Response to tool"));
        context
            .messages
            .push(ContextMessage::assistant("Next message", None));
        context.messages.push(ContextMessage::user("Final message"));

        // Test that a range that would break a tool call chain is adjusted
        let fixture = &context;
        let (actual_start, actual_end) = adjust_range_for_tool_calls(fixture, 2, 3);
        let (expected_start, expected_end) = (1, 3); // Should include the tool call message
        assert_eq!(actual_start, expected_start);
        assert_eq!(actual_end, expected_end);

        // Test that a range at the end is not modified if there are no tool calls
        let (actual_start, actual_end) = adjust_range_for_tool_calls(fixture, 3, 4);
        let (expected_start, expected_end) = (3, 4); // No need to adjust
        assert_eq!(actual_start, expected_start);
        assert_eq!(actual_end, expected_end);
    }

    #[test]
    fn test_find_sequence_with_tool_calls() {
        use crate::{ContextMessage, ToolCallFull, ToolCallId, ToolName};

        // Create a test context with tool call chains
        let mut context = Context::default();

        // Add some initial messages
        context
            .messages
            .push(ContextMessage::user("Initial message"));
        context
            .messages
            .push(ContextMessage::assistant("First response", None));

        // Add a tool call chain
        let tool_call = vec![ToolCallFull {
            name: ToolName::new("test_tool"),
            call_id: Some(ToolCallId::new("1")),
            arguments: serde_json::json!({"arg": "value"}),
        }];

        context
            .messages
            .push(ContextMessage::assistant("Using a tool", Some(tool_call)));
        context
            .messages
            .push(ContextMessage::user("Response to tool"));

        // Add more messages to reach the threshold for compaction
        context
            .messages
            .push(ContextMessage::assistant("Another response", None));
        context
            .messages
            .push(ContextMessage::user("Another message"));
        context
            .messages
            .push(ContextMessage::assistant("Final response", None));

        // Test with preservation window that would normally exclude the tool call
        let fixture = &context;
        let preserve_last_n = 2; // Only preserve the last 2 messages

        // Find a sequence for summarization
        let actual = find_sequence(fixture, preserve_last_n);

        // The sequence should start at the first assistant message (index 1)
        // and end before the last user message (index 5) to preserve the tool call
        // chain
        let expected = Some((1, 3)); // Include both assistant messages and the tool call

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_adjust_range_across_multiple_chains() {
        use crate::{ContextMessage, ToolCallFull, ToolCallId, ToolName};

        // Create a test context with multiple tool call chains
        let mut context = Context::default();

        // Add messages that form multiple tool call chains
        context
            .messages
            .push(ContextMessage::user("Initial message"));

        let tool_call1 = vec![ToolCallFull {
            name: ToolName::new("tool1"),
            call_id: Some(ToolCallId::new("1")),
            arguments: serde_json::json!({"arg": "value1"}),
        }];

        context
            .messages
            .push(ContextMessage::assistant("Using tool1", Some(tool_call1)));
        context
            .messages
            .push(ContextMessage::user("Response to tool1"));
        context
            .messages
            .push(ContextMessage::assistant("Response after tool1", None));

        let tool_call2 = vec![ToolCallFull {
            name: ToolName::new("tool2"),
            call_id: Some(ToolCallId::new("2")),
            arguments: serde_json::json!({"arg": "value2"}),
        }];

        context
            .messages
            .push(ContextMessage::assistant("Using tool2", Some(tool_call2)));
        context
            .messages
            .push(ContextMessage::user("Response to tool2"));
        context
            .messages
            .push(ContextMessage::assistant("Final message", None));

        // Test with a range that splits the second tool call chain
        let fixture = &context;
        let (actual_start, actual_end) = adjust_range_for_tool_calls(fixture, 3, 6);

        // Should adjust to include the complete second tool call chain
        let (expected_start, expected_end) = (3, 6);

        assert_eq!(actual_start, expected_start);
        assert_eq!(actual_end, expected_end);

        // Test with a range that splits the first tool call chain
        let (actual_start, actual_end) = adjust_range_for_tool_calls(fixture, 2, 5);

        // Should adjust to include the first tool call chain
        let (expected_start, expected_end) = (1, 5);

        assert_eq!(actual_start, expected_start);
        assert_eq!(actual_end, expected_end);
    }
}
