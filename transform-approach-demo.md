# Using Transforms for Auto-Compact Functionality

Rather than adding a new `auto_compact` field to the `Agent` struct, we could have leveraged the existing transformation system. Here's how it would work:

## Existing `Transform::Assistant` Variant

The `Transform::Assistant` variant already handles token-based summarization:

```rust
Transform::Assistant {
    // Input template for the transformation
    input: String,
    // Output template after transformation
    output: String,
    // ID of the agent performing the transformation
    agent_id: AgentId,
    // Maximum token limit for the compressed message
    token_limit: usize,
}
```

## How Transforms Are Executed

In the `execute_transform` method of the `Orchestrator`, the system already processes `Transform::Assistant`:

```rust
async fn execute_transform(
    &self,
    transforms: &[Transform],
    mut context: Context,
) -> anyhow::Result<Context> {
    for transform in transforms.iter() {
        match transform {
            Transform::Assistant {
                agent_id,
                token_limit,
                input: input_key,
                output: output_key,
            } => {
                let mut summarize = Summarize::new(&mut context, *token_limit);
                while let Some(mut summary) = summarize.summarize() {
                    let input = Event::new(input_key, summary.get());
                    self.init_agent_with_event(agent_id, &input).await?;

                    if let Some(value) = self.get_last_event(output_key).await? {
                        summary.set(serde_json::to_string(&value)?);
                    }
                }
            }
            // Other transform variants...
        }
    }
    Ok(context)
}
```

## How We Could Implement Auto-Compact Using Transforms

Instead of introducing a new field, we could have extended the existing `Transform` enum with a new `AutoCompact` variant:

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Transform {
    // Existing variants...
    
    /// Automatically compacts the context when token count exceeds a threshold
    AutoCompact {
        // Maximum token limit before compaction
        token_limit: usize,
    },
}
```

Then, in the `execute_transform` method, we could add a new match arm:

```rust
Transform::AutoCompact { token_limit } => {
    let total_tokens = token_count(&context.to_text());
    
    if total_tokens > *token_limit {
        let mut summarize = Summarize::new(&mut context, *token_limit);
        
        // Apply summarization until we're below the threshold
        while let Some(mut summary) = summarize.summarize() {
            let turn_content = summary.get();
            let summary_text = format!("Auto-summarized conversation turn with {} tokens", 
                                      token_count(&turn_content));
            summary.set(summary_text);
        }
        
        debug!(
            conversation_id = %self.conversation_id,
            tokens_before = %total_tokens,
            threshold = %token_limit,
            tokens_after = %token_count(&context.to_text()),
            "Auto-compaction performed"
        );
    }
}
```

## Benefits of the Transform-Based Approach

1. **Consistency**: Uses the existing transformation mechanism instead of adding a new field
2. **Flexibility**: Transformations are applied in a specific order, giving more control
3. **Extensibility**: Easier to add more summarization strategies in the future
4. **Maintainability**: Keeps all context modifications in a single place (the transform system)

## Configuration Example

With this approach, agents would be configured like this:

```yaml
agents:
  my_agent:
    id: "my_agent"
    transforms:
      - type: auto_compact
        token_limit: 10000
```

## Conclusion

While our implementation with the `auto_compact` field works correctly, using the transformation system would have been more aligned with the existing architecture of the codebase. It would have kept all context modification logic within the transformation system rather than adding a separate check in the `init_agent_with_event` method.