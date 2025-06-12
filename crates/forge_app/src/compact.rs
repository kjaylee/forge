use std::sync::Arc;

use forge_domain::{
    Agent, ChatCompletionMessage, ChatCompletionMessageFull, Compact, Context, ContextMessage,
    ResultStreamExt, estimate_token_count, extract_tag_content,
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
        percentage: Option<f64>,
    ) -> anyhow::Result<Context> {
        if let Some(ref compact) = agent.compact {
            debug!(agent_id = %agent.id, "Context compaction triggered");

            match find_sequence(&context, percentage.unwrap_or(compact.percentage))
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
    let total_tokens = messages
        .iter()
        .skip(start_index)
        .map(|msg| estimate_token_count(msg.to_text().len()) as f64)
        .sum::<f64>();
    let token_limit = (total_tokens * percentage).floor();
    let mut accumulated_tokens = 0.0;
    let mut end_index = 0;
    let mut ans = None;

    // Process message groups to find where we exceed the target token count
    for group in context.message_groups(Some(start_index)) {
        let group_tokens: f64 = group
            .iter()
            .map(|msg| estimate_token_count(msg.to_text().len()) as f64)
            .sum();
        accumulated_tokens += group_tokens;
        end_index += group.len();

        if accumulated_tokens > token_limit {
            // We exceeded the token limit, so we stop here
            break;
        }

        // there should be atleast two messages.
        let end_index = start_index.saturating_add(end_index).saturating_sub(1);
        if end_index.saturating_sub(start_index) < 1 {
            continue;
        }
        ans = Some((start_index, end_index));
    }

    ans
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
    /// t - 8 tokens
    /// r - 7 tokens
    /// a - 5 tokens
    #[test]
    fn test_sequence_finding() {
        // Original test cases with detailed calculations

        // Pattern: s-u-a-t-r-u, Total: u(3) + a(5) + tr(15) + u(3) = 26 tokens
        // 35% of 26 = 9.1 tokens, Groups: [u](3) + [a](5) = 8 < 9.1, but adding
        // [tr](15) = 23 > 9.1
        let actual = seq("suatru", 0.35);
        assert_eq!(actual, "s[ua]tru");

        // Pattern: s-u-t-r-u-a-a, Total: u(3) + tr(15) + u(3) + a(5) + a(5) = 31 tokens
        // 25% of 31 = 7.75 tokens, Groups: [u](3) < 7.75, but adding [tr](15) = 18 >
        // 7.75
        let actual = seq("sutruaa", 0.25);
        assert_eq!(actual, "sutruaa");

        // Pattern: s-u-t-r-u-a-a, Total: u(3) + tr(15) + u(3) + a(5) + a(5) = 31 tokens
        // 95% of 31 = 29.45 tokens, Groups: [u](3) + [tr](15) + [u](3) + [a](5) = 26 <
        // 29.45
        let actual = seq("sutruaa", 0.95);
        assert_eq!(actual, "s[utrua]a");

        // Pattern: u-t-r-u-a-a, Total: u(3) + tr(15) + u(3) + a(5) + a(5) = 31 tokens
        // 55% of 31 = 17.05 tokens, Groups: [u](3) < 17.05, but adding [tr](15) = 18 >
        // 17.05
        let actual = seq("utruaa", 0.55);
        assert_eq!(actual, "utruaa");

        // Edge case: 0% percentage should return no sequence
        // Any percentage of 0% means no tokens can be included
        let actual = seq("suatru", 0.0);
        assert_eq!(actual, "suatru");

        // Edge case: 100% percentage should include all non-system messages
        // Pattern: s-u-a-t-r-u, Total: u(3) + a(5) + tr(15) + u(3) = 26 tokens
        // 100% of 26 = 26 tokens, all groups fit: [u](3) + [a](5) + [tr](15) + [u](3) =
        // 26
        let actual = seq("suatru", 1.0);
        assert_eq!(actual, "s[uatru]");

        // Edge case: only system messages should return no sequence
        // Pattern: s-s-s, no non-system messages to process
        let actual = seq("sss", 0.5);
        assert_eq!(actual, "sss");

        // Edge case: empty pattern should return no sequence
        // No messages to process
        let actual = seq("", 0.5);
        assert_eq!(actual, "");

        // Test with only user messages
        // Pattern: u-u-u, Total: u(3) + u(3) + u(3) = 9 tokens
        // 50% of 9 = 4.5 tokens, Groups: [u](3) < 4.5, but adding [u](3) = 6 > 4.5
        let actual = seq("uuu", 0.5);
        assert_eq!(actual, "uuu");

        // Test with tool calls and results pattern - tr is grouped together (15 tokens)
        // Pattern: s-u-t-r-u, Total: u(3) + tr(15) + u(3) = 21 tokens
        // 60% of 21 = 12.6 tokens, Groups: [u](3) < 12.6, but adding [tr](15) = 18 >
        // 12.6
        let actual = seq("sutru", 0.6);
        assert_eq!(actual, "sutru");

        // Test with mixed pattern - tr is grouped, so we get u(3) + tr(15) = 18 tokens
        // Pattern: s-u-t-r-t-r-u, Total: u(3) + tr(15) + tr(15) + u(3) = 36 tokens
        // 40% of 36 = 14.4 tokens, Groups: [u](3) < 14.4, but adding [tr](15) = 18 >
        // 14.4
        let actual = seq("sutrtru", 0.4);
        assert_eq!(actual, "sutrtru");

        // Test with very small percentage
        // Pattern: s-u-a-a-a-a, Total: u(3) + a(5) + a(5) + a(5) + a(5) = 23 tokens
        // 10% of 23 = 2.3 tokens, Groups: [u](3) > 2.3, so no groups fit
        let actual = seq("suaaaa", 0.1);
        assert_eq!(actual, "suaaaa");

        // Test with pattern starting with user message (no system)
        // Pattern: u-a-t-r-u, Total: u(3) + a(5) + tr(15) + u(3) = 26 tokens
        // 40% of 26 = 10.4 tokens, Groups: [u](3) + [a](5) = 8 < 10.4, but adding
        // [tr](15) = 23 > 10.4
        let actual = seq("uatru", 0.4);
        assert_eq!(actual, "[ua]tru");

        // Test with all assistant messages
        // Pattern: s-a-a-a-a, Total: a(5) + a(5) + a(5) + a(5) = 20 tokens
        // 60% of 20 = 12 tokens, Groups: [a](5) + [a](5) = 10 < 12, but adding [a](5) =
        // 15 > 12
        let actual = seq("saaaa", 0.6);
        assert_eq!(actual, "s[aa]aa");

        // Test complex pattern with tool calls - each tr is a group
        // Pattern: s-u-t-r-t-r-a-a, Total: u(3) + tr(15) + tr(15) + a(5) + a(5) = 43
        // tokens 50% of 43 = 21.5 tokens, Groups: [u](3) + [tr](15) = 18 <
        // 21.5, but adding [tr](15) = 33 > 21.5
        let actual = seq("sutrtraa", 0.5);
        assert_eq!(actual, "s[utr]traa");

        // Test pattern with single non-system message
        // Pattern: s-u, Total: u(3) = 3 tokens
        // 50% of 3 = 1.5 tokens, Groups: [u](3) > 1.5, so no groups fit
        let actual = seq("su", 0.5);
        assert_eq!(actual, "su");

        // Test pattern with alternating messages
        // Pattern: s-u-a-u-a-u-a, Total: u(3) + a(5) + u(3) + a(5) + u(3) + a(5) = 24
        // tokens 30% of 24 = 7.2 tokens, Groups: [u](3) < 7.2, but adding
        // [a](5) = 8 > 7.2
        let actual = seq("suauaua", 0.3);
        assert_eq!(actual, "suauaua");

        // Test with tool call followed by multiple results (if that's possible)
        // Pattern: s-u-t-r-u, Total: u(3) + tr(15) + u(3) = 21 tokens
        // 50% of 21 = 10.5 tokens, Groups: [u](3) < 10.5, but adding [tr](15) = 18 >
        // 10.5
        let actual = seq("sutru", 0.5);
        assert_eq!(actual, "sutru");

        // Test where tool call group fits within percentage
        // Pattern: s-u-t-r, Total: u(3) + tr(15) = 18 tokens
        // 90% of 18 = 16.2 tokens, Groups: [u](3) < 16.2, but adding [tr](15) = 18 >
        // 16.2
        let actual = seq("sutr", 0.9);
        assert_eq!(actual, "sutr");

        // Test where tool call group actually fits within percentage
        // Pattern: s-u-t-r, Total: u(3) + tr(15) = 18 tokens
        // 100% of 18 = 18 tokens, Groups: [u](3) + [tr](15) = 18 = 18, so both fit
        // exactly
        let actual = seq("sutr", 1.0);
        assert_eq!(actual, "s[utr]");
    }
}
