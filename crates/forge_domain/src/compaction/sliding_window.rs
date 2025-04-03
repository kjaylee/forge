use std::cmp::max;

/// Sliding window strategy for context compaction
///
/// This strategy implements a sliding window approach that keeps the most
/// recent messages while preserving important context at the beginning of the
/// conversation like system messages and initial setup. It also preserves tool
/// call chains to maintain coherence in multi-step tool interactions.
use anyhow::Result;
use tracing::debug;

use super::strategy::CompactionImpact;
use super::CompactionStrategy;
use crate::compaction::adjust_range::adjust_range_for_tool_calls;
use crate::{Compact, Context, ContextMessage, Role};

/// Compaction strategy that implements a sliding window approach with special
/// handling for system messages and tool call chains.
pub struct SlidingWindowStrategy;

impl CompactionStrategy for SlidingWindowStrategy {
    fn id(&self) -> &'static str {
        "sliding_window"
    }

    fn is_applicable(&self, _compact: &Compact, context: &Context) -> bool {
        // Sliding window can always be applied as long as there's more than
        // one message and preservation parameters are set
        context.messages.len() > 1
    }

    /// Compacts the context using a sliding window approach
    ///
    /// Preserves the most recent messages along with system messages and
    /// important context at the beginning. It also ensures that tool call
    /// chains are not broken.
    async fn compact(
        &self,
        compact: &Compact,
        context: Context,
    ) -> Result<(Context, CompactionImpact)> {
        let preserve_last_n = compact.retention_window;
        let original_message_count = context.messages.len();

        // Handle case where we should preserve everything
        if preserve_last_n >= original_message_count {
            let impact =
                CompactionImpact::new(original_message_count, original_message_count, Some(0));
            return Ok((context, impact));
        }

        // Start with an empty context and preserve system messages
        let mut new_messages: Vec<ContextMessage> = Vec::new();

        // Always keep system messages
        for msg in context.messages.iter() {
            if msg.has_role(Role::System) {
                new_messages.push(msg.clone());
            }
        }

        // Find the starting point for the sliding window
        let start_idx = max(0, original_message_count.saturating_sub(preserve_last_n));
        debug!(
            strategy = self.id(),
            original_messages = original_message_count,
            preserve_last_n,
            start_idx,
            "Calculating sliding window"
        );

        // Adjust to avoid breaking tool call chains using the shared utility
        let (adjusted_start_idx, _) =
            adjust_range_for_tool_calls(&context, start_idx, original_message_count - 1);

        debug!(
            strategy = self.id(),
            original_start_idx = start_idx,
            adjusted_start_idx,
            "Adjusted start index to preserve tool call chains"
        );

        // Add the remaining messages from the sliding window
        for i in adjusted_start_idx..original_message_count {
            // Avoid adding duplicate system messages
            let msg = &context.messages[i];
            if !msg.has_role(Role::System) || !new_messages.iter().any(|m| m.has_role(Role::System))
            {
                new_messages.push(msg.clone());
            }
        }

        let mut new_context = context.clone();
        new_context.messages = new_messages;

        let impact = CompactionImpact::new(
            original_message_count,
            new_context.messages.len(),
            None, // We don't have token counts available
        );

        Ok((new_context, impact))
    }
}
