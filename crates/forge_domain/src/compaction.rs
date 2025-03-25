use std::sync::Arc;

use anyhow::Result;
use futures::StreamExt;
use tracing::debug;

use crate::{
    Agent, ChatCompletionMessage, Context, ContextMessage, ProviderService, Role, Services,
    TemplateService,
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
        if !self.should_perform_compaction(agent, &context) {
            return Ok(context);
        }

        debug!(
            agent_id = %agent.id,
            "Context compaction triggered"
        );
        
        // Identify the first compressible sequence
        if let Some(sequence) = self.identify_first_compressible_sequence(&context) {
            debug!(
                agent_id = %agent.id,
                sequence_start = sequence.0,
                sequence_end = sequence.1,
                "Compressing assistant message sequence"
            );
            
            // Compress just this sequence
            self.compress_single_sequence(agent, context, sequence).await
        } else {
            debug!(agent_id = %agent.id, "No compressible sequences found");
            Ok(context)
        }
    }

    /// Identifies the first sequence of assistant messages that can be compressed (2+ consecutive messages)
    fn identify_first_compressible_sequence(&self, context: &Context) -> Option<(usize, usize)> {
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
            if end - start > 0 {  // More than 1 message
                return Some((start, end));
            }
        }
        
        None // No compressible sequence found
    }

    /// Compress a single identified sequence of assistant messages
    async fn compress_single_sequence(
        &self, 
        agent: &Agent, 
        original_context: Context, 
        sequence: (usize, usize)
    ) -> Result<Context> {
        let messages = original_context.messages;
        let (start, end) = sequence;
        
        // Extract the sequence to summarize
        let sequence_messages = &messages[start..=end];
        
        // Generate summary for this sequence
        let summary = self.generate_summary_for_sequence(agent, sequence_messages).await?;
        
        // Build a new context with the sequence replaced by the summary
        let mut compacted_messages = Vec::new();
        
        // Add messages before the sequence
        compacted_messages.extend(messages[0..start].to_vec());
        
        // Add the summary as a single assistant message
        compacted_messages.push(ContextMessage::assistant(summary, None));
        
        // Add messages after the sequence
        if end + 1 < messages.len() {
            compacted_messages.extend(messages[end+1..].to_vec());
        }
        
        // Build the new context
        let mut compacted_context = Context::default();
        
        // Add system message if present in original context
        if let Some(system_msg) = messages.first().filter(|m| m.has_role(Role::System)) {
            compacted_context = compacted_context.add_message(system_msg.clone());
        }
        
        // Add all other processed messages
        for msg in compacted_messages.into_iter().filter(|m| !m.has_role(Role::System)) {
            compacted_context = compacted_context.add_message(msg);
        }

        // Preserve tools and tool_choice from the original context
        compacted_context.tools = original_context.tools;
        compacted_context.tool_choice = original_context.tool_choice;
        
        Ok(compacted_context)
    }

    /// Generate a summary for a specific sequence of assistant messages
    async fn generate_summary_for_sequence(
        &self, 
        agent: &Agent, 
        messages: &[ContextMessage]
    ) -> Result<String> {
        let compact = agent.compact.as_ref().unwrap();

        // Create a temporary context with just the sequence for summarization
        let mut sequence_context = Context::default();
        for msg in messages {
            sequence_context = sequence_context.add_message(msg.clone());
        }
        
        // Render the summarization prompt
        let prompt = self
            .services
            .template_service()
            .render_summarization(agent, &sequence_context)
            .await?;

        let message = ContextMessage::user(prompt);
        let summary_context = Context::default().add_message(message);

        // Get summary from the provider
        let response = self
            .services
            .provider_service()
            .chat(&compact.model, summary_context)
            .await?;

        self.collect_completion_stream_content(response).await
    }

    /// Determines whether context compaction should be performed
    fn should_perform_compaction(&self, agent: &Agent, context: &Context) -> bool {
        agent
            .compact
            .as_ref()
            .map(|compact| compact.should_compact(context))
            .unwrap_or(false)
    }

    /// Collects the content from a streaming ChatCompletionMessage response
    async fn collect_completion_stream_content<T>(&self, mut stream: T) -> Result<String>
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

        Ok(result_content)
    }
}