# Tool Call Chain Preservation Logic Extraction

## Objective

Extract and consolidate the logic for preserving tool call chains in the compaction strategies to improve maintainability and ensure consistent behavior. Currently, both the Summarization and Sliding Window strategies have separate implementations for handling tool calls, which could lead to inconsistent behavior and makes maintenance more difficult.

## Implementation Plan

1. **Create a shared utility function in the compaction module**:
   - Add a new function such as `adjust_range_for_tool_calls` in `mod.rs`
   - The function should:
     ```rust
     /// Adjusts a proposed range to ensure tool call chains are preserved
     /// 
     /// This prevents compaction from breaking up related tool calls and responses
     /// which could cause context loss for the agent.
     pub fn adjust_range_for_tool_calls(context: &Context, start_idx: usize, end_idx: usize) -> (usize, usize) {
         // Implementation details here
     }
     ```
   - The function should examine messages in the range and adjust boundaries to prevent breaking tool call chains
   - It should handle both simple cases (single tool call) and complex chains (tool call → user response → assistant response)

2. **Refactor the sliding window strategy**:
   - Replace the current tool call chain preservation logic:
   ```rust
   // Current implementation
   let mut adjusted_start_idx = start_idx;
   while adjusted_start_idx > 0 {
       let prev_msg = context.messages.get(adjusted_start_idx - 1);
       let curr_msg = context.messages.get(adjusted_start_idx);
       
       match (prev_msg, curr_msg) {
           (Some(prev), Some(curr)) if prev.has_tool_call() && curr.has_role(Role::User) => {
               adjusted_start_idx -= 1;
           }
           _ => break,
       }
   }
   ```
   - Replace with:
   ```rust
   // New implementation
   let (adjusted_start_idx, _) = adjust_range_for_tool_calls(&context, start_idx, original_message_count - 1);
   ```

3. **Update the find_sequence function**:
   - Refactor the current simple tool call check:
   ```rust
   // Current implementation
   if messages
       .get(max_len - 1)
       .is_some_and(|msg| msg.has_tool_call())
   {
       max_len -= 1;
   }
   ```
   - Modify to use the shared utility:
   ```rust
   // Determine the initial range
   // ...existing code...
   
   // Adjust the range to respect tool call chains
   if let Some((start, end)) = range {
       let (adjusted_start, adjusted_end) = adjust_range_for_tool_calls(context, start, end);
       return Some((adjusted_start, adjusted_end));
   }
   ```

4. **Implement robust detection of tool call chains**:
   - The utility function should recognize different patterns:
     - Single tool call messages
     - Tool call + user response pairs
     - Complete chains: tool call → user response → assistant response
   - The algorithm should:
     1. Scan backward from the start boundary to include complete chains
     2. Scan forward from the end boundary to include incomplete chains
     3. Be conservative - include more messages rather than break a potential chain

5. **Add comprehensive test cases**:
   - Create tests for the new utility function directly
   - Test with various conversation patterns:
     - Tool calls without responses
     - Complete tool call chains
     - Multiple consecutive tool call chains
     - Tool calls at range boundaries
   - Verify that both strategies produce consistent results

## Verification Criteria

1. **Functional Correctness**:
   - All existing tests continue to pass
   - New tests for the shared utility function pass
   - Manual verification with sample conversations shows tool call chains are preserved

2. **Code Quality**:
   - The shared utility function has clear documentation
   - Both strategies use the shared utility function consistently
   - No code duplication for tool call chain detection

3. **Behavior Verification**:
   - Summarization strategy correctly identifies and preserves tool call chains
   - Sliding Window strategy correctly preserves tool call chains
   - Edge cases (e.g., conversation starts with a tool call) are handled correctly

4. **Performance**:
   - The refactored code does not significantly impact performance
   - The utility function is efficient and avoids unnecessary iterations

By extracting this logic, we'll ensure that both compaction strategies handle tool call preservation consistently, making the code more maintainable and reducing the risk of bugs when either strategy is modified.