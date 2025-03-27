use std::sync::Arc;

use anyhow::Result;
use futures::StreamExt;
use tracing::debug;

use crate::{
    extract_tag_content, Agent, ChatCompletionMessage, Compact, Context, ContextMessage,
    ProviderService, Role, Services, TemplateService,
};

/// Handles the compaction of conversation contexts to manage token usage
#[derive(Clone)]
pub struct ContextCompactor<Services> {
    services: Arc<Services>,
}

impl<S: Services> ContextCompactor<S> {
    /// Creates a new ContextCompactor instance
    pub fn new(services: Arc<S>) -> Self {
        Self { services }
    }

    /// Check if compaction is needed and compact the context if so
    pub async fn compact_context(&self, agent: &Agent, context: Context) -> Result<Context> {
        // Early return if compaction not needed

        if let Some(ref compact) = agent.compact {
            debug!(agent_id = %agent.id, "Context compaction triggered");

            // Identify and compress the first compressible sequence
            match identify_first_compressible_sequence(&context, compact.retention_window) {
                Some(sequence) => {
                    debug!(
                        agent_id = %agent.id,
                        sequence_start = sequence.0,
                        sequence_end = sequence.1,
                        "Compressing assistant message sequence"
                    );
                    self.compress_single_sequence(compact, context, sequence)
                        .await
                }
                None => {
                    debug!(agent_id = %agent.id, "No compressible sequences found");
                    Ok(context)
                }
            }
        } else {
            Ok(context)
        }
    }

    /// Compress a single identified sequence of assistant messages
    async fn compress_single_sequence(
        &self,
        compact: &Compact,
        mut context: Context,
        sequence: (usize, usize),
    ) -> Result<Context> {
        let (start, end) = sequence;

        // Extract the sequence to summarize
        let sequence_messages = &context.messages[start..=end];

        // Generate summary for this sequence
        let summary = self
            .generate_summary_for_sequence(compact, sequence_messages)
            .await?;

        // Log the summary for debugging
        debug!(summary = %summary, "Created context compaction summary");

        // Replace the sequence with a single summary message using splice
        // This removes the sequence and inserts the summary message in-place
        context.messages.splice(
            start..=end,
            std::iter::once(ContextMessage::assistant(summary, None)),
        );

        Ok(context)
    }

    /// Generate a summary for a specific sequence of assistant messages
    async fn generate_summary_for_sequence(
        &self,
        compact: &Compact,
        messages: &[ContextMessage],
    ) -> Result<String> {
        // Create a temporary context with just the sequence for summarization
        let sequence_context = messages
            .iter()
            .fold(Context::default(), |ctx, msg| ctx.add_message(msg.clone()));

        // Render the summarization prompt
        let prompt = self
            .services
            .template_service()
            .render_summarization(compact, &sequence_context)
            .await?;

        // Create a new context
        let mut context = Context::default().add_message(ContextMessage::user(prompt));

        // Set max_tokens for summary
        if let Some(max_token) = compact.max_tokens {
            context = context.max_tokens(max_token);
        }

        // Get summary from the provider
        let response = self
            .services
            .provider_service()
            .chat(&compact.model, context)
            .await?;

        self.collect_completion_stream_content(compact, response)
            .await
    }

    /// Collects the content from a streaming ChatCompletionMessage response
    /// and extracts text within the configured tag if present
    async fn collect_completion_stream_content<T>(
        &self,
        compact: &Compact,
        mut stream: T,
    ) -> Result<String>
    where
        T: futures::Stream<Item = Result<ChatCompletionMessage>> + Unpin,
    {
        let mut result_content = String::new();

        while let Some(message_result) = stream.next().await {
            let message = message_result?;
            if let Some(content) = message.content {
                result_content.push_str(content.as_str());
            }
        }

        // Extract content from within configured tags if present and if tag is
        // configured
        if let Some(tag_name) = &compact.summary_tag {
            if let Some(extracted) = extract_tag_content(&result_content, tag_name) {
                return Ok(extracted.to_string());
            }
        }

        // If no tag extraction performed, return the original content
        Ok(result_content)
    }
}

/// Identifies the first sequence of compressible messages (assistant messages
/// and tool results) that can be compressed (2+ consecutive messages)
/// taking into account the preserve_last_n_messages setting from the agent
fn identify_first_compressible_sequence(
    context: &Context,
    preserve_last_n: usize,
) -> Option<(usize, usize)> {
    // Get all compressible sequences, considering the preservation window
    find_compressible_sequences(context, preserve_last_n)
        .into_iter()
        .next()
}

/// Determines if a message is compressible (assistant or tool result)
fn is_compressible(message: &ContextMessage) -> bool {
    message.has_role(Role::Assistant) || matches!(message, ContextMessage::ToolMessage(_))
}

/// Finds all valid compressible sequences in the context, respecting the
/// preservation window
fn find_compressible_sequences(context: &Context, preserve_last_n: usize) -> Vec<(usize, usize)> {
    let messages = &context.messages;

    // Calculate the index before which messages can be considered for compression
    let compressible_end_idx = messages.len().saturating_sub(preserve_last_n);

    // Early return if there are no messages available for compression
    if compressible_end_idx == 0 {
        return Vec::new();
    }

    // Find all sequences of compressible messages
    find_sequences_by_predicate(&messages[0..compressible_end_idx], is_compressible)
        .into_iter()
        // Filter for sequences with at least 2 messages
        .filter(|(start, end)| end > start)
        .collect()
}

/// General-purpose function to find sequences of elements matching a predicate
fn find_sequences_by_predicate<T, F>(elements: &[T], predicate: F) -> Vec<(usize, usize)>
where
    F: Fn(&T) -> bool,
{
    let mut sequences = Vec::new();
    let mut current_sequence_start: Option<usize> = None;

    // Iterate through all elements
    for (i, element) in elements.iter().enumerate() {
        if predicate(element) {
            // Start a new sequence or continue current one
            if current_sequence_start.is_none() {
                current_sequence_start = Some(i);
            }
        } else {
            // End of sequence - if we had one in progress, record it
            if let Some(start) = current_sequence_start.take() {
                sequences.push((start, i - 1));
            }
        }
    }

    // Check for a sequence that ends at the last element
    if let Some(start) = current_sequence_start {
        sequences.push((start, elements.len() - 1));
    }

    sequences
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::{ToolCallFull, ToolCallId, ToolName, ToolResult};

    #[test]
    fn test_identify_first_compressible_sequence() {
        // Create a context with a sequence of assistant messages
        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant("Assistant message 1", None))
            .add_message(ContextMessage::assistant("Assistant message 2", None))
            .add_message(ContextMessage::assistant("Assistant message 3", None))
            .add_message(ContextMessage::user("User message 2"))
            .add_message(ContextMessage::assistant("Assistant message 4", None));

        // The first sequence is from index 2 to 4 (assistant messages 1, 2, and 3)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 2);
        assert_eq!(end, 4);
    }

    #[test]
    fn test_no_compressible_sequence() {
        // Create a context with no sequence of multiple assistant messages
        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant("Assistant message 1", None))
            .add_message(ContextMessage::user("User message 2"))
            .add_message(ContextMessage::assistant("Assistant message 2", None))
            .add_message(ContextMessage::user("User message 3"))
            .add_message(ContextMessage::assistant("Assistant message 3", None));

        // There are no sequences of multiple assistant messages
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_none());
    }

    #[test]
    fn test_sequence_at_end_of_context() {
        // Create a context with a sequence at the end
        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant("Assistant message 1", None))
            .add_message(ContextMessage::user("User message 2"))
            .add_message(ContextMessage::assistant("Assistant message 2", None))
            .add_message(ContextMessage::assistant("Assistant message 3", None));

        // The sequence is at the end (indices 4-5)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 4);
        assert_eq!(end, 5);
    }

    #[test]
    fn test_identify_sequence_with_tool_calls() {
        // Create a context with assistant messages containing tool calls
        let tool_call = ToolCallFull {
            name: ToolName::new("tool_forge_fs_read"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"path": "/test/path"}),
        };

        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant(
                "Assistant message with tool call",
                Some(vec![tool_call.clone()]),
            ))
            .add_message(ContextMessage::assistant(
                "Assistant message with another tool call",
                Some(vec![tool_call.clone()]),
            ))
            .add_message(ContextMessage::user("User message 2"));

        // The sequence is from index 2 to 3 (both assistant messages with tool calls)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 2);
        assert_eq!(end, 3);
    }

    #[test]
    fn test_identify_sequence_with_tool_results() {
        // Create a context with assistant messages and tool results
        let tool_call = ToolCallFull {
            name: ToolName::new("tool_forge_fs_read"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"path": "/test/path"}),
        };

        let tool_result = ToolResult::new(ToolName::new("tool_forge_fs_read"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"content": "File content"}).to_string());

        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant(
                "Assistant message with tool call",
                Some(vec![tool_call]),
            ))
            .add_message(ContextMessage::tool_result(tool_result))
            .add_message(ContextMessage::assistant(
                "Assistant follow-up message",
                None,
            ))
            .add_message(ContextMessage::assistant("Another assistant message", None))
            .add_message(ContextMessage::user("User message 2"));

        // Now tool results are considered compressible
        // The sequence is from index 2 to 5 (assistant + tool + 2 assistant messages)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 2);
        assert_eq!(end, 5);
    }

    #[test]
    fn test_mixed_assistant_and_tool_messages() {
        // Create a context where we strictly alternate assistant/tool and user messages
        let tool_call1 = ToolCallFull {
            name: ToolName::new("tool_forge_fs_read"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"path": "/test/path1"}),
        };

        let tool_call2 = ToolCallFull {
            name: ToolName::new("tool_forge_fs_search"),
            call_id: Some(ToolCallId::new("call_456")),
            arguments: json!({"path": "/test/path2", "regex": "pattern"}),
        };

        let tool_result1 = ToolResult::new(ToolName::new("tool_forge_fs_read"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"content": "File content 1"}).to_string());

        let tool_result2 = ToolResult::new(ToolName::new("tool_forge_fs_search"))
            .call_id(ToolCallId::new("call_456"))
            .success(json!({"matches": ["match1", "match2"]}).to_string());

        // Create a context where we strictly alternate assistant and non-assistant
        // messages to ensure no compressible sequence forms
        let context = Context::default()
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant(
                "Assistant message with tool call",
                Some(vec![tool_call1]),
            ))
            .add_message(ContextMessage::tool_result(tool_result1))
            .add_message(ContextMessage::user("User follow-up question"))
            .add_message(ContextMessage::assistant(
                "Assistant with another tool call",
                Some(vec![tool_call2]),
            ))
            .add_message(ContextMessage::tool_result(tool_result2))
            .add_message(ContextMessage::user("User message 2"));

        // With the new logic, we now have a compressible sequence from index 1-2
        // (assistant + tool result)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 1);
        assert_eq!(end, 2);
    }

    #[test]
    fn test_consecutive_assistant_messages_with_tools() {
        // Test when we have consecutive assistant messages with tool calls
        // followed by tool results but the assistant messages themselves are
        // consecutive
        let tool_call1 = ToolCallFull {
            name: ToolName::new("tool_forge_fs_read"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"path": "/test/path1"}),
        };

        let tool_call2 = ToolCallFull {
            name: ToolName::new("tool_forge_fs_search"),
            call_id: Some(ToolCallId::new("call_456")),
            arguments: json!({"path": "/test/path2", "regex": "pattern"}),
        };

        let tool_result1 = ToolResult::new(ToolName::new("tool_forge_fs_read"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"content": "File content 1"}).to_string());

        let tool_result2 = ToolResult::new(ToolName::new("tool_forge_fs_search"))
            .call_id(ToolCallId::new("call_456"))
            .success(json!({"matches": ["match1", "match2"]}).to_string());

        let context = Context::default()
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant(
                "Assistant message with tool call",
                Some(vec![tool_call1.clone()]),
            ))
            .add_message(ContextMessage::assistant(
                "Another assistant message",
                Some(vec![tool_call2.clone()]),
            ))
            .add_message(ContextMessage::assistant("Third assistant message", None))
            .add_message(ContextMessage::tool_result(tool_result1))
            .add_message(ContextMessage::tool_result(tool_result2))
            .add_message(ContextMessage::user("User message 2"));

        // The sequence now includes both assistant messages and tool results (indices
        // 1-5)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 1);
        assert_eq!(end, 5);
    }

    #[test]
    fn test_only_tool_results() {
        // Test when we have just tool results in sequence
        let tool_result1 = ToolResult::new(ToolName::new("tool_forge_fs_read"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"content": "File content 1"}).to_string());

        let tool_result2 = ToolResult::new(ToolName::new("tool_forge_fs_search"))
            .call_id(ToolCallId::new("call_456"))
            .success(json!({"matches": ["match1", "match2"]}).to_string());

        let context = Context::default()
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::tool_result(tool_result1))
            .add_message(ContextMessage::tool_result(tool_result2))
            .add_message(ContextMessage::user("User message 2"));

        // The sequence is the two tool results (indices 1-2)
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 1);
        assert_eq!(end, 2);
    }

    #[test]
    fn test_mixed_assistant_and_single_tool() {
        // Create a context with an assistant message and a tool result,
        // but each preceded by user messages so they're not consecutive
        let tool_call = ToolCallFull {
            name: ToolName::new("tool_forge_fs_read"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"path": "/test/path"}),
        };

        let tool_result = ToolResult::new(ToolName::new("tool_forge_fs_read"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"content": "File content 1"}).to_string());

        let context = Context::default()
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant(
                "Assistant message with tool call",
                Some(vec![tool_call]),
            ))
            .add_message(ContextMessage::user("User intermediate message"))
            .add_message(ContextMessage::tool_result(tool_result))
            .add_message(ContextMessage::user("User message 2"));

        // No compressible sequence as each potential message is separated by a user
        // message
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_none());
    }
    #[test]
    fn test_preserve_last_n_messages() {
        // Create a context with multiple sequences that could be compressed
        let context = Context::default()
            .add_message(ContextMessage::system("System message"))
            .add_message(ContextMessage::user("User message 1"))
            .add_message(ContextMessage::assistant("Assistant message 1", None)) // 2
            .add_message(ContextMessage::assistant("Assistant message 2", None)) // 3
            .add_message(ContextMessage::assistant("Assistant message 3", None)) // 4
            .add_message(ContextMessage::user("User message 2")) // 5
            .add_message(ContextMessage::assistant("Assistant message 4", None)) // 6
            .add_message(ContextMessage::assistant("Assistant message 5", None)); // 7

        // Without preservation, we'd compress messages 2-4
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());
        let (start, end) = sequence.unwrap();
        assert_eq!(start, 2);
        assert_eq!(end, 4);

        // With preserve_last_n = 3, we should preserve the last 3 messages (indices 5,
        // 6, 7) So we should still get the sequence at 2-4
        let sequence = identify_first_compressible_sequence(&context, 3);
        assert!(sequence.is_some());
        let (start, end) = sequence.unwrap();
        assert_eq!(start, 2);
        assert_eq!(end, 4);

        // With preserve_last_n = 5, we should preserve indices 3-7
        // So we should get no compressible sequence, since we can only consider indices
        // 0-2
        let sequence = identify_first_compressible_sequence(&context, 5);
        assert!(sequence.is_none());

        // With preserve_last_n = 8 (more than total messages), we should get no
        // compressible sequence
        let sequence = identify_first_compressible_sequence(&context, 8);
        assert!(sequence.is_none());
    }
    #[test]
    fn test_preserve_last_n_with_sequence_at_end() {
        // Create a context with a sequence at the end
        let context = Context::default()
            .add_message(ContextMessage::system("System message")) // 0
            .add_message(ContextMessage::user("User message 1")) // 1
            .add_message(ContextMessage::assistant("Assistant message 1", None)) // 2
            .add_message(ContextMessage::user("User message 2")) // 3
            .add_message(ContextMessage::assistant("Assistant message 2", None)) // 4
            .add_message(ContextMessage::assistant("Assistant message 3", None)) // 5
            .add_message(ContextMessage::assistant("Assistant message 4", None)); // 6

        // Without preservation, we'd compress the sequence at indices 4-6
        let sequence = identify_first_compressible_sequence(&context, 0);
        assert!(sequence.is_some());
        let (start, end) = sequence.unwrap();
        assert_eq!(start, 4);
        assert_eq!(end, 6);

        // With preserve_last_n = 2, we should preserve indices 5-6
        // So the compressible sequence should be index 4 only, which is not enough for
        // compression
        let sequence = identify_first_compressible_sequence(&context, 2);
        assert!(sequence.is_none());

        // With preserve_last_n = 1, we should preserve index 6
        // So the compressible sequence should be indices 4-5
        let sequence = identify_first_compressible_sequence(&context, 1);
        assert!(sequence.is_some());
        let (start, end) = sequence.unwrap();
        assert_eq!(start, 4);
        assert_eq!(end, 5);
    }

    #[test]
    fn test_is_compressible() {
        // Test assistant message
        let assistant_message = ContextMessage::assistant("Test message", None);
        assert!(is_compressible(&assistant_message));

        // Test tool result
        let tool_result = ContextMessage::tool_result(
            ToolResult::new(ToolName::new("test_tool")).success("test result".to_string()),
        );
        assert!(is_compressible(&tool_result));

        // Test user message (not compressible)
        let user_message = ContextMessage::user("User message");
        assert!(!is_compressible(&user_message));

        // Test system message (not compressible)
        let system_message = ContextMessage::system("System message");
        assert!(!is_compressible(&system_message));
    }

    #[test]
    fn test_find_sequences_by_predicate() {
        // Test with a simple vector of numbers, finding sequences of even numbers
        let numbers = vec![1, 2, 4, 6, 7, 8, 10, 11, 12];

        let sequences = find_sequences_by_predicate(&numbers, |&n| n % 2 == 0);

        assert_eq!(sequences.len(), 3);
        assert_eq!(sequences[0], (1, 3)); // 2, 4, 6
        assert_eq!(sequences[1], (5, 6)); // 8, 10
        assert_eq!(sequences[2], (8, 8)); // 12
    }
}
