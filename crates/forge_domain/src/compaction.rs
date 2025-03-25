use std::sync::Arc;

use anyhow::Result;
use futures::StreamExt;
use tracing::debug;

use crate::{Agent, Context, ContextMessage, ProviderService, Services, TemplateService};

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
        if let Some(ref compact) = agent.compact {
            if compact.should_compact(&context) {
                debug!(
                    agent_id = %agent.id,
                    "Context compaction triggered"
                );
                let prompt = self
                    .services
                    .template_service()
                    .render_summarization(agent, &context)
                    .await?;

                let message = ContextMessage::user(prompt);

                let mut context = Context::default();
                context = context.add_message(message);
                let response = self
                    .services
                    .provider_service()
                    .chat(&compact.model, context)
                    .await?;

                let mut result_content = String::new();
                let mut stream = response;

                while let Some(message_result) = stream.next().await {
                    let message = message_result?;
                    if let Some(content) = message.content {
                        result_content.push_str(content.as_str());
                    }
                }

                let context = self
                    .init_agent_context(agent)
                    .await?
                    .add_message(ContextMessage::assistant(result_content, None));

                Ok(context)
            } else {
                Ok(context)
            }
        } else {
            Ok(context)
        }
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
