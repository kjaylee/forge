use std::sync::Arc;

use anyhow::Result;
use futures::StreamExt;
use tracing::debug;

use crate::{
    extract_tag_content, Agent, ChatCompletionMessage, Context, ContextMessage, ProviderService,
    Role, Services, TemplateService,
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
        if !self.should_perform_compaction(agent, &context) {
            return Ok(context);
        }

        debug!(agent_id = %agent.id, "Context compaction triggered");

        // Identify and compress the first compressible sequence
        match identify_first_compressible_sequence(&context) {
            Some(sequence) => {
                debug!(
                    agent_id = %agent.id,
                    sequence_start = sequence.0,
                    sequence_end = sequence.1,
                    "Compressing assistant message sequence"
                );
                self.compress_single_sequence(agent, context, sequence)
                    .await
            }
            None => {
                debug!(agent_id = %agent.id, "No compressible sequences found");
                Ok(context)
            }
        }
    }

    /// Compress a single identified sequence of assistant messages
    async fn compress_single_sequence(
        &self,
        agent: &Agent,
        mut context: Context,
        sequence: (usize, usize),
    ) -> Result<Context> {
        let (start, end) = sequence;

        // Extract the sequence to summarize
        let sequence_messages = &context.messages[start..=end];

        // Generate summary for this sequence
        let summary = self
            .generate_summary_for_sequence(agent, sequence_messages)
            .await?;

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
        agent: &Agent,
        messages: &[ContextMessage],
    ) -> Result<String> {
        let compact = agent.compact.as_ref().unwrap();

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

        self.collect_completion_stream_content(agent, response)
            .await
    }

    /// Determines whether context compaction should be performed
    fn should_perform_compaction(&self, agent: &Agent, context: &Context) -> bool {
        agent
            .compact
            .as_ref()
            .is_some_and(|compact| compact.should_compact(context))
    }

    /// Collects the content from a streaming ChatCompletionMessage response
    /// and extracts text within the configured tag if present
    async fn collect_completion_stream_content<T>(
        &self,
        agent: &Agent,
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
        if let Some(agent_compact) = &agent.compact {
            if let Some(tag_name) = &agent_compact.summary_tag {
                if let Some(extracted) = extract_tag_content(&result_content, tag_name) {
                    return Ok(extracted.to_string());
                }
            }
        }

        // If no tag extraction performed, return the original content
        Ok(result_content)
    }
}

/// Identifies the first sequence of assistant messages that can be compressed
/// (2+ consecutive messages)
fn identify_first_compressible_sequence(context: &Context) -> Option<(usize, usize)> {
    let messages = &context.messages;
    let mut current_sequence_start: Option<usize> = None;

    for (i, message) in messages.iter().enumerate() {
        if message.has_role(Role::Assistant) {
            // Start a new sequence or continue current one
            if current_sequence_start.is_none() {
                current_sequence_start = Some(i);
            }
        } else {
            // End of a potential sequence
            if let Some(start) = current_sequence_start {
                // Only compress sequences with more than 1 assistant message
                if i - start > 1 {
                    return Some((start, i - 1));
                }
                current_sequence_start = None;
            }
        }
    }

    // Check for a sequence at the end
    if let Some(start) = current_sequence_start {
        let end = messages.len() - 1;
        if end - start > 0 {
            // More than 1 message
            return Some((start, end));
        }
    }

    None // No compressible sequence found
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let sequence = identify_first_compressible_sequence(&context);
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
        let sequence = identify_first_compressible_sequence(&context);
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
        let sequence = identify_first_compressible_sequence(&context);
        assert!(sequence.is_some());

        let (start, end) = sequence.unwrap();
        assert_eq!(start, 4);
        assert_eq!(end, 5);
    }
}
