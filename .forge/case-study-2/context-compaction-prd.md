# Context Compaction Feature: PRD

## Overview
Automatically summarize and compact AI conversation history to reduce token usage while maintaining conversation coherence.

## Problem
Long conversations:
- Consume excessive tokens
- Slow down responses
- Hit context limits
- Create reasoning issues from context overload

## Solution Concept
The core idea is to intelligently compress conversation history by:

1. **Selective Compression**: Only compress sequences of assistant messages and tool results, leaving user messages intact to preserve conversation flow and intent.

2. **Incremental Approach**: Instead of compressing everything at once, identify and compress only the earliest sequence of compressible messages, working sequentially over time.

3. **Summarization via AI**: Use the same AI models to summarize their own previous responses, creating a "digest" of their reasoning and outputs.

4. **Recency Preservation**: Always keep the most recent messages untouched to maintain conversation context and continuity.

5. **Configurable Thresholds**: Allow agents to decide when compaction should trigger based on different conversation metrics.

## Key Features

### Compaction Triggers
- Token count threshold
- Message count threshold
- Turn count threshold

### Message Handling
- Configurable retention window (default: 6 messages)
- Preserve user and system messages
- Only compress assistant messages and tool results

### Configuration
```yaml
compact:
  max_tokens: 2000
  token_threshold: 60000
  retention_window: 6
  model: google/gemini-2.0-flash-001
  prompt: "{{> system-prompt-context-summarizer.hbs }}"
  summary_tag: "summary"
```

## How It Works

### The Compaction Process
1. **Detection**: As conversation progresses, continually check if any compaction thresholds are exceeded.

2. **Identification**: Find the earliest sequence of consecutive assistant/tool messages that can be compressed.

3. **Summarization**: Take this sequence and ask the AI to summarize it into a single, concise message that captures the key information.

4. **Replacement**: Replace the entire sequence with the single summary message, reducing token count while preserving meaning.

5. **Repeat**: Continue this process over time whenever thresholds are exceeded, maintaining efficient context size.

### Example Scenario
Consider a debugging conversation that includes multiple tool calls and assistant explanations:

```
User: "Can you debug this code?"
Assistant: "Let me take a look." + (Tool call to read file)
Tool Result: (File contents)
Assistant: "I found the issue..." + (Detailed explanation)
Assistant: "Let me fix it." + (Tool call to patch file)
Tool Result: (Success message)
Assistant: "The fix is applied. Here's what I changed..."
User: "Can you explain why that fixed it?"
```

After compaction, this might become:

```
User: "Can you debug this code?"
Assistant: "I debugged the code by identifying an issue with error handling, then fixed it by adding proper try/catch blocks and applied the patch successfully."
User: "Can you explain why that fixed it?"
```