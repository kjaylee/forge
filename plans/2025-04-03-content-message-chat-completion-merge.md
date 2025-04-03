# ContentMessage and ChatCompletionResult Merge

**Date**: 2025-04-03

## Objective

Merge ContentMessage and ChatCompletionResult classes as they contain similar functionality and don't need to be separate.

## Implementation Details


1. Enhanced ContentMessage with Usage Information:
   * Added `usage: Option<Usage>` field to ContentMessage
   * Updated all factory methods to include usage parameter with None as default
   * Added a new `from_completion` method to ContentMessage to create an instance from content, tool calls, and usage
   * Added `assistant_with_usage` method to ContextMessage to support creating messages with usage info
2. Removed ChatCompletionResult:
   * Deleted the ChatCompletionResult struct
   * Updated the collect_messages method to return ContentMessage directly
   * Modified references in init_agent and other methods to use ContentMessage instead of ChatCompletionResult
3. Updated Flow:
   * Modified the way tool calls are extracted from ContentMessage
   * Changed the way usage information is accessed in the compactor

## Benefits


1. **Simplified Code Structure**: Removed redundancy by combining similar structures
2. **Unified Interface**: Now there's a single structure for managing content, tool calls, and usage data
3. **Better Information Flow**: Usage information now passes through the ContentMessage structure
4. **Cleaner API**: More consistent API with all assistant content in one structure

## Testing

The implementation should be tested by:


1. Ensuring all functionality remains intact
2. Verifying that usage information is properly preserved
3. Confirming that tool calls continue to work correctly
4. Validating that context compaction still functions as expected


