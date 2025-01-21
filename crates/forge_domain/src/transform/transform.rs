use std::sync::Arc;

use anyhow::Result;
use tokio_stream::StreamExt;

use crate::{BreakPoint, Context, ContextMessage, ModelId, ProviderService};

#[async_trait::async_trait]
pub trait Transform {
    async fn transform(&self, ctx: Context, bp: &BreakPoint) -> Result<Context>;
}

/// Remove messages that match the breakpoint
pub struct RemoveMessages;

#[async_trait::async_trait]
impl Transform for RemoveMessages {
    async fn transform(&self, mut ctx: Context, bp: &BreakPoint) -> Result<Context> {
        // Get indices of messages to remove
        let indices = bp.get_breakpoints(&ctx);
        if indices.is_empty() {
            return Ok(ctx);
        }

        // Remove messages in reverse order to maintain correct indices
        let mut indices: Vec<_> = indices.into_iter().collect();
        indices.sort_unstable();
        indices.reverse();

        for index in indices {
            if index >= ctx.messages.len() {
                continue;
            }
            ctx.messages.remove(index);
        }

        Ok(ctx)
    }
}

/// Summarize messages that match the breakpoint
pub struct SummarizeMessages {
    provider: Arc<dyn ProviderService>,
    model_id: ModelId,
}

impl SummarizeMessages {
    pub fn new(provider: Arc<dyn ProviderService>, model_id: ModelId) -> Self {
        Self { provider, model_id }
    }
}

#[async_trait::async_trait]
impl Transform for SummarizeMessages {
    async fn transform(&self, mut ctx: Context, bp: &BreakPoint) -> Result<Context> {
        // Get indices of messages to summarize
        let indices = bp.get_breakpoints(&ctx);
        if indices.is_empty() {
            return Ok(ctx);
        }

        // Extract messages to summarize
        let messages_to_summarize: Vec<_> =
            indices.iter().map(|&i| ctx.messages[i].clone()).collect();

        // Create summarization context with prompt
        let prompt = include_str!("./prompts/summarize.md");
        let mut summarize_ctx = Context::default().set_system_message(prompt);
        summarize_ctx.messages.extend(messages_to_summarize);

        // Get summary from provider
        let mut stream = self.provider.chat(&self.model_id, summarize_ctx).await?;

        let mut summary = String::new();
        while let Some(result) = stream.next().await {
            match result {
                Ok(msg) => {
                    if let Some(content) = msg.content {
                        summary.push_str(content.as_str());
                    }
                }
                Err(e) => return Err(e),
            }
        }

        // Replace messages with summary in reverse order
        let mut indices: Vec<_> = indices.into_iter().collect();
        indices.sort_unstable();
        indices.reverse();

        // Replace first occurrence with summary and remove the rest
        if let Some(&first_index) = indices.last() {
            ctx.messages[first_index] = ContextMessage::assistant(summary, None);

            // Remove remaining messages
            for &index in indices.iter().rev().skip(1) {
                ctx.messages.remove(index);
            }
        }

        Ok(ctx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MessageRole;
    use crate::{ChatCompletionMessage, Model, Parameters, Role};

    #[tokio::test]
    async fn test_remove_messages() {
        let ctx = Context::default()
            .add_message(ContextMessage::user("message 1"))
            .add_message(ContextMessage::assistant("message 2", None))
            .add_message(ContextMessage::user("message 3"));

        // Remove assistant messages
        let bp = BreakPoint::Role(MessageRole::Role(Role::Assistant));
        let transform = RemoveMessages;

        let result = transform.transform(ctx.clone(), &bp).await.unwrap();
        assert_eq!(result.messages.len(), 2);
        assert_eq!(result.messages[0].content(), "message 1".to_string());
        assert_eq!(result.messages[1].content(), "message 3".to_string());
    }

    #[tokio::test]
    async fn test_remove_messages_empty_breakpoint() {
        let ctx = Context::default()
            .add_message(ContextMessage::user("message 1"))
            .add_message(ContextMessage::user("message 2"));

        // Remove assistant messages (none exist)
        let bp = BreakPoint::Role(MessageRole::Role(Role::Assistant));
        let transform = RemoveMessages;

        let result = transform.transform(ctx.clone(), &bp).await.unwrap();
        assert_eq!(result.messages.len(), 2);
    }

    #[tokio::test]
    async fn test_remove_messages_complex_breakpoint() {
        let ctx = Context::default()
            .add_message(ContextMessage::user("message 1"))
            .add_message(ContextMessage::assistant("message 2", None))
            .add_message(ContextMessage::user("message 3"))
            .add_message(ContextMessage::assistant("message 4", None));

        // Remove assistant messages after first user message
        let bp = BreakPoint::And(
            Box::new(BreakPoint::Role(MessageRole::Role(Role::Assistant))),
            Box::new(BreakPoint::After(
                Box::new(BreakPoint::Role(MessageRole::Role(Role::User))),
                Box::new(BreakPoint::Role(MessageRole::Role(Role::Assistant))),
            )),
        );

        let transform = RemoveMessages;
        let result = transform.transform(ctx.clone(), &bp).await.unwrap();

        assert_eq!(result.messages.len(), 2);
        assert_eq!(result.messages[0].content(), "message 1".to_string());
        assert_eq!(result.messages[1].content(), "message 3".to_string());
    }

    // Mock provider service for testing
    #[derive(Clone)]
    struct MockProvider {
        summary: String,
    }

    #[async_trait::async_trait]
    impl ProviderService for MockProvider {
        async fn chat(
            &self,
            _model: &ModelId,
            _ctx: Context,
        ) -> anyhow::Result<
            futures::stream::BoxStream<'static, anyhow::Result<ChatCompletionMessage>>,
        > {
            let msg = ChatCompletionMessage::default().content_full(&self.summary);
            Ok(Box::pin(futures::stream::once(async { Ok(msg) })))
        }

        async fn models(&self) -> anyhow::Result<Vec<Model>> {
            Ok(vec![])
        }

        async fn parameters(&self, _model: &ModelId) -> anyhow::Result<Parameters> {
            Ok(Parameters::default())
        }
    }

    #[tokio::test]
    async fn test_summarize_messages() {
        let ctx = Context::default()
            .add_message(ContextMessage::user("message 1"))
            .add_message(ContextMessage::assistant("message 2", None))
            .add_message(ContextMessage::user("message 3"));

        let mock_provider = Arc::new(MockProvider { summary: "Summary of messages".to_string() });

        // Summarize assistant messages
        let bp = BreakPoint::Role(MessageRole::Role(Role::Assistant));
        let transform = SummarizeMessages::new(mock_provider, ModelId::new("test-model"));

        let result = transform.transform(ctx.clone(), &bp).await.unwrap();
        assert_eq!(result.messages.len(), 3);
        assert_eq!(result.messages[0].content(), "message 1".to_string());
        assert_eq!(
            result.messages[1].content(),
            "Summary of messages".to_string()
        );
        assert_eq!(result.messages[2].content(), "message 3".to_string());
    }

    #[tokio::test]
    async fn test_summarize_messages_empty_breakpoint() {
        let ctx = Context::default()
            .add_message(ContextMessage::user("message 1"))
            .add_message(ContextMessage::user("message 2"));

        let mock_provider = Arc::new(MockProvider { summary: "Summary of messages".to_string() });

        // Summarize assistant messages (none exist)
        let bp = BreakPoint::Role(MessageRole::Role(Role::Assistant));
        let transform = SummarizeMessages::new(mock_provider, ModelId::new("test-model"));

        let result = transform.transform(ctx.clone(), &bp).await.unwrap();
        assert_eq!(result.messages.len(), 2);
    }

    #[tokio::test]
    async fn test_summarize_messages_complex_breakpoint() {
        let ctx = Context::default()
            .add_message(ContextMessage::user("message 1"))
            .add_message(ContextMessage::assistant("message 2", None))
            .add_message(ContextMessage::user("message 3"))
            .add_message(ContextMessage::assistant("message 4", None));

        let mock_provider = Arc::new(MockProvider { summary: "Summary of messages".to_string() });

        // Summarize messages after first user message
        let bp = BreakPoint::After(
            Box::new(BreakPoint::Role(MessageRole::Role(Role::User))),
            Box::new(BreakPoint::Role(MessageRole::Role(Role::Assistant))),
        );

        let transform = SummarizeMessages::new(mock_provider, ModelId::new("test-model"));
        let result = transform.transform(ctx.clone(), &bp).await.unwrap();

        assert_eq!(result.messages.len(), 3);
        assert_eq!(result.messages[0].content(), "message 1".to_string());
        assert_eq!(
            result.messages[1].content(),
            "Summary of messages".to_string()
        );
        assert_eq!(result.messages[2].content(), "message 3".to_string());
    }
}
