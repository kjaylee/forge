# Agent Context Sliding Window Compaction

## Objective

Implement a sliding window mechanism for context compaction in the Forge codebase. This feature will augment the existing compaction system, providing a fallback mechanism when traditional summarization-based compaction cannot be applied. The sliding window approach will forcefully drop the oldest messages when no compressible sequences are available, ensuring that context size remains manageable under all conditions.

## Background

The current context compaction system in Forge:
1. Identifies sequences of messages that can be compressed
2. Compresses those sequences by creating a summary to replace them
3. Does not have a fallback mechanism when no compressible sequences are found

For context to remain manageable in all scenarios, we need to implement a sliding window approach that will drop messages when summarization isn't possible.

## Implementation Plan

### 1. Enhance the `compact_context` Method

Modify the existing method to include a fallback path when no compressible sequences are found:

```rust
pub async fn compact_context(&self, agent: &Agent, context: Context) -> Result<Context> {
    if let Some(ref compact) = agent.compact {
        // Ensure that compaction conditions are met
        if !compact.should_compact(&context) {
            return Ok(context);
        }

        debug!(agent_id = %agent.id, "Context compaction triggered");

        // Identify and compress the first compressible sequence
        match find_sequence(&context, compact.retention_window)
            .into_iter()
            .next()
        {
            Some(sequence) => {
                // Existing summarization approach
                self.compress_single_sequence(compact, context, sequence)
                    .await
            }
            None => {
                // New sliding window approach
                debug!(agent_id = %agent.id, "No compressible sequences found, falling back to sliding window");
                self.drop_oldest_messages(compact, context)
            }
        }
    } else {
        Ok(context)
    }
}
```

### 2. Implement `drop_oldest_messages` Method

This new method will implement the sliding window logic:

```rust
/// Drops oldest messages in the context until thresholds are satisfied
/// Follows constraints: first message after dropping must be a user message,
/// and tool call+result pairs must be dropped atomically
fn drop_oldest_messages(&self, compact: &Compact, mut context: Context) -> Result<Context> {
    // Early return for empty contexts
    if context.messages.is_empty() {
        return Ok(context);
    }
    
    // Continue dropping messages until thresholds are met or we can't drop anymore
    while compact.should_compact(&context) {
        let before_count = context.messages.len();
        
        // Find the next viable drop boundary
        let drop_boundary = self.calculate_drop_boundary(&context.messages);
        
        if drop_boundary == 0 {
            // Can't drop anymore without violating constraints
            debug!("Cannot drop more messages without violating constraints");
            break;
        }
        
        // Perform the drop
        info!(
            "Sliding window compaction: dropping {} oldest messages", 
            drop_boundary
        );
        context.messages = context.messages.split_off(drop_boundary);
        
        // Check if we actually dropped anything
        if context.messages.len() == before_count {
            break;
        }
    }
    
    Ok(context)
}
```

### 3. Implement Helper Functions for Drop Boundary Calculation

```rust
/// Calculates the optimal boundary for dropping messages
/// Returns the index up to which messages can be dropped
fn calculate_drop_boundary(&self, messages: &[ContextMessage]) -> usize {
    // Preserve system messages at the beginning
    let start_idx = self.find_first_non_system_message(messages);
    
    // Find the next user message after our starting point
    if let Some(user_msg_idx) = self.find_next_user_message(messages, start_idx) {
        // Check if there's a tool call chain before this user message
        if user_msg_idx > 0 && self.is_part_of_tool_chain(messages, user_msg_idx - 1) {
            // Find the start of this tool chain
            let mut chain_start = user_msg_idx - 1;
            while chain_start > 0 && self.is_part_of_tool_chain(messages, chain_start - 1) {
                chain_start -= 1;
            }
            return chain_start;
        }
        
        // No tool chain, we can drop everything before this user message
        return user_msg_idx;
    }
    
    // No user message found, can't drop without violating constraints
    0
}

/// Finds the first message that is not a system message
fn find_first_non_system_message(&self, messages: &[ContextMessage]) -> usize {
    for (idx, msg) in messages.iter().enumerate() {
        if !msg.has_role(Role::System) {
            return idx;
        }
    }
    messages.len()
}

/// Finds the next user message starting from a given index
fn find_next_user_message(&self, messages: &[ContextMessage], start_idx: usize) -> Option<usize> {
    for idx in start_idx..messages.len() {
        if messages[idx].has_role(Role::User) {
            return Some(idx);
        }
    }
    None
}

/// Checks if a message is part of a tool call chain
fn is_part_of_tool_chain(&self, messages: &[ContextMessage], idx: usize) -> bool {
    // A message is part of a tool chain if:
    // 1. It has a tool call
    // 2. It is a tool result
    
    if idx >= messages.len() {
        return false;
    }
    
    match &messages[idx] {
        ContextMessage::ContentMessage(msg) if msg.tool_calls.is_some() => true,
        ContextMessage::ToolMessage(_) => true,
        _ => false,
    }
}
```

### 4. Tests Implementation

Add comprehensive tests to verify the sliding window implementation works correctly:

```rust
#[cfg(test)]
mod sliding_window_tests {
    use pretty_assertions::assert_eq;

    use super::*;
    
    // Test helper to create a basic compact config
    fn test_compact() -> Compact {
        Compact::new(ModelId::new("test"))
            .message_threshold(Some(5))
            .retention_window(0)
    }
    
    #[test]
    fn test_basic_sliding_window() {
        // Create a context with no compressible sequences but exceeding thresholds
        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant("Assistant message 1", None))
            .add_message(ContextMessage::user("User message 2"))
            .add_message(ContextMessage::assistant("Assistant message 2", None))
            .add_message(ContextMessage::user("User message 3"));
            
        // Mock services for testing
        let services = MockServices::new();
        let compactor = ContextCompactor::new(Arc::new(services));
        
        // Apply sliding window compaction
        let result = compactor.drop_oldest_messages(&test_compact(), context).unwrap();
        
        // Should drop older messages, starting with a user message
        assert!(result.messages.len() < 6);
        assert!(result.messages[0].has_role(Role::User));
    }
    
    #[test]
    fn test_atomic_tool_call_dropping() {
        // Create a tool call and result
        let tool_call = ToolCallFull {
            name: ToolName::new("some_tool"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"arg": "value"}),
        };
        
        let tool_result = ToolResult::new(ToolName::new("some_tool"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"result": "success"}).to_string());
            
        // Create a context with tool calls
        let context = Context::default()
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant("Assistant with tool", Some(vec![tool_call])))
            .add_message(ContextMessage::tool_result(tool_result))
            .add_message(ContextMessage::user("User message 2"))
            .add_message(ContextMessage::assistant("Final response", None));
            
        // Mock services for testing
        let services = MockServices::new();
        let compactor = ContextCompactor::new(Arc::new(services));
        
        // Apply sliding window compaction
        let result = compactor.drop_oldest_messages(&test_compact(), context).unwrap();
            
        // Should either keep both tool call and result, or drop both
        let has_tool_call = result.messages.iter()
            .any(|msg| match msg {
                ContextMessage::ContentMessage(m) => m.tool_calls.is_some(),
                _ => false,
            });
            
        let has_tool_result = result.messages.iter()
            .any(|msg| matches!(msg, ContextMessage::ToolMessage(_)));
            
        // Either both should be present or neither should be present
        assert_eq!(has_tool_call, has_tool_result);
    }
    
    #[test]
    fn test_multiple_drop_passes() {
        // Create a large context
        let mut context = Context::default()
            .add_message(ContextMessage::system("System message"));
            
        // Add many messages to force multiple drop passes
        for i in 1..15 {
            context = context
                .add_message(ContextMessage::user(format!("User message {}", i)))
                .add_message(ContextMessage::assistant(format!("Assistant message {}", i), None));
        }
            
        // Create a compact with strict thresholds
        let compact = Compact::new(ModelId::new("test"))
            .message_threshold(Some(10))
            .retention_window(0);
            
        // Mock services for testing
        let services = MockServices::new();
        let compactor = ContextCompactor::new(Arc::new(services));
            
        // Apply sliding window compaction
        let result = compactor.drop_oldest_messages(&compact, context).unwrap();
            
        // Should have dropped enough messages to be below threshold
        assert!(result.messages.len() <= 10);
        // First message should be a user message
        assert!(result.messages[0].has_role(Role::User));
    }
    
    #[test]
    fn test_edge_cases() {
        // Mock services for testing
        let services = MockServices::new();
        let compactor = ContextCompactor::new(Arc::new(services));
        let compact = test_compact();
        
        // Empty context
        let empty_context = Context::default();
        let result = compactor.drop_oldest_messages(&compact, empty_context).unwrap();
        assert_eq!(result.messages.len(), 0);
        
        // Only system messages
        let system_only = Context::default()
            .add_message(ContextMessage::system("System message 1"))
            .add_message(ContextMessage::system("System message 2"));
        let result = compactor.drop_oldest_messages(&compact, system_only).unwrap();
        assert_eq!(result.messages.len(), 2); // Should preserve system messages
        
        // No user messages
        let no_user = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::assistant("Assistant message", None));
        let result = compactor.drop_oldest_messages(&compact, no_user).unwrap();
        assert_eq!(result.messages.len(), 2); // Can't drop without user message
    }
}
```

### 5. Integration with Existing Codebase

The implementation will be integrated seamlessly with the existing compaction system. It will not alter the behavior for cases where traditional summarization works, but will provide a reliable fallback mechanism when summarization isn't possible.

## Verification Criteria

The implementation will be considered successful if these criteria are met:

1. **Functionality**:
   - Context size is kept under control even when no compressible sequences are available
   - Messages are dropped correctly following all specified constraints

2. **Constraints Respect**:
   - The first message after dropping must be a user message
   - Tool call and result pairs must be handled atomically

3. **Integration**:
   - Existing compaction functionality continues to work
   - The sliding window logic only activates when needed

4. **Testing**:
   - All tests pass, including edge cases
   - Test coverage is comprehensive

5. **Code Quality**:
   - Implementation follows Rust idioms and project standards
   - Appropriate logging is added for debugging

## Additional Considerations

1. **Performance Impact**: The sliding window implementation should be efficient and not significantly impact performance when processing large contexts.

2. **Continued Improvement**: This implementation serves as a foundation for future enhancements to the context compaction system. Further optimizations might include more sophisticated algorithms for determining which messages are most important to preserve.

3. **Documentation**: Comprehensive documentation will be added to explain how the sliding window mechanism works and how it interacts with the existing compaction system.

## Conclusion

The sliding window compaction feature will significantly enhance the robustness of the Forge context management system by ensuring context size remains manageable in all scenarios. This is a critical feature for maintaining reliable operation when dealing with complex and extended conversations.