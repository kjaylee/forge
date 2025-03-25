use std::sync::Arc;

use anyhow::Result;
use futures::StreamExt;
use tracing::debug;

use crate::{Agent, ChatCompletionMessage, Context, ContextMessage, ProviderService, Services, TemplateService};

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

        let summary = self.generate_summary(agent, &context).await?;
        let compacted_context = self.build_compacted_context(agent, summary).await?;
        
        Ok(compacted_context)
    }

    /// Determines whether context compaction should be performed
    fn should_perform_compaction(&self, agent: &Agent, context: &Context) -> bool {
        agent.compact
            .as_ref()
            .map(|compact| compact.should_compact(context))
            .unwrap_or(false)
    }

    /// Generates a summary of the current context using the provider service
    async fn generate_summary(&self, agent: &Agent, context: &Context) -> Result<String> {
        let compact = agent.compact.as_ref().unwrap();
        
        let prompt = self
            .services
            .template_service()
            .render_summarization(agent, context)
            .await?;

        let message = ContextMessage::user(prompt);
        let summary_context = Context::default().add_message(message);
        
        let response = self
            .services
            .provider_service()
            .chat(&compact.model, summary_context)
            .await?;

        self.collect_completion_stream_content(response).await
    }

    /// Collects the content from a streaming ChatCompletionMessage response
    async fn collect_completion_stream_content<T>(&self, mut stream: T) -> Result<String> 
    where 
        T: futures::Stream<Item = Result<ChatCompletionMessage>> + Unpin
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

    /// Builds a new context with the generated summary
    async fn build_compacted_context(&self, agent: &Agent, summary: String) -> Result<Context> {
        let context = self
            .init_agent_context(agent)
            .await?
            .add_message(ContextMessage::assistant(summary, None));

        Ok(context)
    }

    /// Initialize agent context with appropriate tools and system prompt
    async fn init_agent_context(&self, agent: &Agent) -> Result<Context> {
        let mut context = Context::default();

        if let Some(system_prompt) = &agent.system_prompt {
            let system_message = self
                .services
                .template_service()
                .render_system(agent, system_prompt)
                .await?;

            context = context.set_first_system_message(system_message);
        }

        Ok(context)
    }
}