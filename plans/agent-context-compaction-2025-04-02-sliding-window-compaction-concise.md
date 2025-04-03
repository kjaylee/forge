# Agent Context Sliding Window Compaction - Concise Plan

## Objective

Enhance the Forge context compaction system with a sliding window mechanism that forcefully drops oldest messages when traditional summarization methods cannot be applied, while ensuring:


1. The first message after dropping is a user message
2. Tool call and result pairs are removed atomically
3. Thresholds are satisfied through continuous dropping if necessary

## Implementation Plan

### 1. Enhance the `ContextCompactor` class

Modify the `compact_context` method to include a sliding window fallback:

```rust
pub async fn compact_context(&self, agent: &Agent, context: Context) -> Result<Context> {
    if let Some(ref compact) = agent.compact {
        if !compact.should_compact(&context) {
            return Ok(context);
        }

        // Try traditional summarization first
        match find_sequence(&context, compact.retention_window).into_iter().next() {
            Some(sequence) => {
                // Existing summarization approach
                self.compress_single_sequence(compact, context, sequence).await
            }
            None => {
                // New sliding window approach
                debug!(agent_id = %agent.id, "Falling back to sliding window");
                self.drop_oldest_messages(compact, context)
            }
        }
    } else {
        Ok(context)
    }
}
```

### 2. Implement core sliding window logic

Add the `drop_oldest_messages` method to handle forced message dropping:

```rust
fn drop_oldest_messages(&self, compact: &Compact, mut context: Context) -> Result<Context> {
    // Early return for empty contexts
    if context.messages.is_empty() {
        return Ok(context);
    }
    
    // Continue dropping until thresholds are met
    while compact.should_compact(&context) {
        // Find optimal drop boundary
        let drop_boundary = self.calculate_drop_boundary(&context.messages);
        
        if drop_boundary == 0 {
            // Can't drop anymore without violating constraints
            break;
        }
        
        // Perform the drop operation
        info!("Dropping {} oldest messages", drop_boundary);
        context.messages = context.messages.split_off(drop_boundary);
        
        // Check if we're still above thresholds
        if !compact.should_compact(&context) {
            break;
        }
    }
    
    Ok(context)
}
```

### 3. Implement boundary calculation logic

```rust
fn calculate_drop_boundary(&self, messages: &[ContextMessage]) -> usize {
    // Find first non-system message as starting point
    let start_idx = messages.iter()
        .position(|msg| !msg.has_role(Role::System))
        .unwrap_or(0);
    
    // Find the first user message that will become our new first message
    if let Some(user_idx) = messages.iter()
        .enumerate()
        .skip(start_idx)
        .find(|(_, msg)| msg.has_role(Role::User))
        .map(|(i, _)| i)
    {
        // Check for tool call chains that need to be kept intact
        if self.has_tool_chain_before(messages, user_idx) {
            return self.find_tool_chain_start(messages, user_idx);
        }
        
        return user_idx;
    }
    
    // Couldn't find a suitable boundary
    0
}
```

### 4. Helper functions for tool chain detection

```rust
fn has_tool_chain_before(&self, messages: &[ContextMessage], idx: usize) -> bool {
    if idx == 0 {
        return false;
    }
    
    let prev_idx = idx - 1;
    match &messages[prev_idx] {
        ContextMessage::ContentMessage(msg) if msg.tool_calls.is_some() => true,
        ContextMessage::ToolMessage(_) => true,
        _ => false,
    }
}

fn find_tool_chain_start(&self, messages: &[ContextMessage], end_idx: usize) -> usize {
    let mut start_idx = end_idx;
    
    // Walk backwards to find the start of the chain
    while start_idx > 0 {
        let prev_idx = start_idx - 1;
        let is_tool_related = match &messages[prev_idx] {
            ContextMessage::ContentMessage(msg) => msg.tool_calls.is_some(),
            ContextMessage::ToolMessage(_) => true,
            _ => false,
        };
        
        if !is_tool_related {
            break;
        }
        
        start_idx = prev_idx;
    }
    
    start_idx
}
```

## Testing Strategy


1. **Basic sliding window functionality**:
   * Test dropping messages when no compressible sequences exist
   * Verify first message after dropping is a user message
2. **Tool call atomicity**:
   * Test dropping with tool call + result pairs
   * Verify pairs are never split
3. **Multi-threshold handling**:
   * Test with multiple thresholds
   * Verify dropping continues until all thresholds are satisfied
4. **Edge cases**:
   * Empty context
   * Context with only system messages
   * No user messages in the context
   * Very large contexts requiring multiple dropping passes

## Verification Criteria


1. Context size stays below thresholds even when traditional summarization isn't possible
2. First message after dropping is always a user message
3. Tool call and result pairs are never split
4. All tests pass without regression
5. Implementation is clean, efficient, and well-documented


