use crate::{Context, Role};

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

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::compaction::strategy::CompactionImpact;

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
