use std::sync::Arc;

use forge_domain::{
    Agent, ChatCompletionMessage, ChatCompletionMessageFull, Compact, Context, ContextMessage,
    ResultStreamExt, Role, ToolValue, extract_tag_content, find_compact_sequence,
};
use futures::Stream;
use tracing::{debug, info};

use crate::agent::AgentService;
use crate::template::Templates;

/// A service dedicated to handling context compaction.
pub struct Compactor<S> {
    services: Arc<S>,
}

impl<S: AgentService> Compactor<S> {
    pub fn new(services: Arc<S>) -> Self {
        Self { services }
    }

    /// Apply compaction to the context if requested.
    pub async fn compact_context(
        &self,
        agent: &Agent,
        context: Context,
    ) -> anyhow::Result<Context> {
        if let Some(ref compact) = agent.compact {
            debug!(agent_id = %agent.id, "Context compaction triggered");

            match find_compact_sequence(&context, compact.retention_window)
                .into_iter()
                .next()
            {
                Some(sequence) => {
                    debug!(agent_id = %agent.id, "Compressing sequence");
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

    /// Compress a single identified sequence of assistant messages.
    async fn compress_single_sequence(
        &self,
        compact: &Compact,
        mut context: Context,
        sequence: (usize, usize),
    ) -> anyhow::Result<Context> {
        let (start, end) = sequence;

        let sequence_messages = &context.messages[start..=end].to_vec();

        let summary = self
            .generate_summary_for_sequence(compact, sequence_messages)
            .await?;

        info!(
            summary = %summary,
            sequence_start = sequence.0,
            sequence_end = sequence.1,
            sequence_length = sequence_messages.len(),
            "Created context compaction summary"
        );

        let summary = Templates::render(
            "{{> partial-summary-frame.hbs}}",
            &serde_json::json!({ "summary": summary }),
        )?;

        context.messages.splice(
            start..=end,
            std::iter::once(ContextMessage::user(summary, None)),
        );

        Ok(context)
    }

    /// Generate a summary for a specific sequence of assistant messages.
    async fn generate_summary_for_sequence(
        &self,
        compact: &Compact,
        messages: &[ContextMessage],
    ) -> anyhow::Result<String> {
        let sequence_context = messages
            .iter()
            .fold(Context::default(), |ctx, msg| ctx.add_message(msg.clone()));

        let summary_tag = compact.summary_tag.as_ref().cloned().unwrap_or_default();
        let ctx = serde_json::json!({
            "context": sequence_context.to_text(),
            "summary_tag": summary_tag
        });

        let prompt = Templates::render(
            compact
                .prompt
                .as_deref()
                .unwrap_or("{{> system-prompt-context-summarizer.hbs}}"),
            &ctx,
        )?;

        let mut context = Context::default()
            .add_message(ContextMessage::user(prompt, compact.model.clone().into()));

        if let Some(max_token) = compact.max_tokens {
            context = context.max_tokens(max_token);
        }

        let response = self.services.chat(&compact.model, context).await?;

        self.collect_completion_stream_content(compact, response)
            .await
    }

    /// Collects the content from a streaming ChatCompletionMessage response.
    async fn collect_completion_stream_content(
        &self,
        compact: &Compact,
        stream: impl Stream<Item = anyhow::Result<ChatCompletionMessage>>
        + std::marker::Unpin
        + ResultStreamExt<anyhow::Error>,
    ) -> anyhow::Result<String> {
        let ChatCompletionMessageFull { content, .. } = stream.into_full(false).await?;
        if let Some(extracted) = extract_tag_content(
            &content,
            compact
                .summary_tag
                .as_ref()
                .cloned()
                .unwrap_or_default()
                .as_str(),
        ) {
            return Ok(extracted.to_string());
        }

        Ok(content)
    }
}

/// Find the first sequence of messages that should be compacted based on token
/// percentage.
fn find_sequence(context: &Context, percentage: f64) -> Option<(usize, usize)> {
    let messages = &context.messages;
    if messages.is_empty() || percentage <= 0.0 || percentage > 1.0 {
        return None;
    }

    // Find the first non-system message to start compaction from
    let start_index = messages
        .iter()
        .position(|msg| !msg.has_role(forge_domain::Role::System))?;

    // Calculate total tokens from the start index onwards
    let total_tokens: f64 = messages.iter().skip(start_index).map(count_tokens).sum();
    let token_limit = (total_tokens * percentage).floor();
    let mut accumulated_tokens = 0.0;
    let mut end_index = 0;
    let mut ans = None;

    // Process message groups to find where we exceed the target token count
    for group in context.message_groups(Some(start_index)) {
        let group_tokens: f64 = group.iter().map(count_tokens).sum();
        accumulated_tokens += group_tokens;
        end_index += group.len();
        if accumulated_tokens <= token_limit {
            ans = Some((
                start_index,
                start_index.saturating_add(end_index).saturating_sub(1),
            ));
        } else {
            break;
        }
    }

    ans
}

/// Estimates the number of tokens in a message using character-based
/// approximation.
/// # Reference
/// https://github.com/openai/codex/blob/main/codex-cli/src/utils/approximate-tokens-used.ts
fn count_tokens(message: &ContextMessage) -> f64 {
    let char_count = match message {
        ContextMessage::Text(text_message)
            if matches!(text_message.role, Role::User | Role::Assistant) =>
        {
            text_message.content.chars().count()
        }
        ContextMessage::Tool(tool_result) => tool_result
            .output
            .values
            .iter()
            .map(|result| match result {
                ToolValue::Text(text) => text.chars().count(),
                _ => 0,
            })
            .sum(),
        _ => 0,
    };

    // Convert character count to token estimate using 4:1 ratio, then round up
    (char_count as f64 / 4.0).ceil()
}

#[cfg(test)]
mod tests {
    use forge_domain::{ModelId, ToolCallFull, ToolCallId, ToolName, ToolResult};
    use serde_json::json;

    use super::*;

    fn seq(pattern: impl ToString, percentage: f64) -> String {
        let model_id = ModelId::new("gpt-4");
        let pattern = pattern.to_string();

        let tool_call = ToolCallFull {
            name: ToolName::new("forge_tool_fs_read"),
            call_id: Some(ToolCallId::new("call_123")),
            arguments: json!({"path": "/test/path"}),
        };

        let tool_result = ToolResult::new(ToolName::new("forge_tool_fs_read"))
            .call_id(ToolCallId::new("call_123"))
            .success(json!({"content": "File content"}).to_string());

        let mut context = Context::default();

        for c in pattern.chars() {
            match c {
                's' => context = context.add_message(ContextMessage::system("System message")),
                'u' => {
                    context = context.add_message(ContextMessage::user(
                        "User message",
                        model_id.clone().into(),
                    ))
                }
                'a' => {
                    context =
                        context.add_message(ContextMessage::assistant("Assistant message", None))
                }
                't' => {
                    context = context.add_message(ContextMessage::assistant(
                        "Assistant message with tool call",
                        Some(vec![tool_call.clone()]),
                    ))
                }
                'r' => {
                    context = context.add_message(ContextMessage::tool_result(tool_result.clone()))
                }
                _ => panic!("Invalid character in test pattern: {c}"),
            }
        }

        let sequence = find_sequence(&context, percentage);

        let mut result = pattern.clone();
        if let Some((start, end)) = sequence {
            result.insert(start, '[');
            result.insert(end + 2, ']');
        }

        result
    }

    /// u - 3 tokens
    /// t and r - 15 tokens
    #[test]
    fn test_sequence_finding() {
        let actual = seq("suatru", 0.35);
        assert_eq!(actual, "s[ua]tru");

        let actual = seq("sutruaa", 0.25);
        assert_eq!(actual, "s[u]truaa");

        let actual = seq("sutruaa", 0.95);
        assert_eq!(actual, "s[utrua]a");

        let actual = seq("utruaa", 0.55);
        assert_eq!(actual, "[u]truaa");
    }
}
