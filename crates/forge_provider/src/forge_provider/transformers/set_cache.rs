use forge_domain::Transformer;

use crate::forge_provider::request::{Request, Role};

/// Transformer that caches the last user/system message for supported models
pub struct SetCache;

impl Transformer for SetCache {
    type Value = Request;

    fn transform(&mut self, mut request: Self::Value) -> Self::Value {
        if let Some(messages) = request.messages.as_mut() {
            let mut last_was_user = false;
            let mut cache_positions = Vec::new();
            for (i, message) in messages.iter().enumerate() {
                if message.role == Role::User {
                    if !last_was_user {
                        cache_positions.push(i);
                    }
                    last_was_user = true;
                } else if message.role == Role::Assistant {
                    last_was_user = false;
                } else if message.role == Role::System {
                    cache_positions.push(i);
                    last_was_user = false;
                }
            }

            for pos in cache_positions.into_iter().rev().skip(2).take(2) {
                if let Some(ref content) = messages[pos].content {
                    messages[pos].content = Some(content.clone().cached());
                }
            }

            request
        } else {
            request
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use forge_domain::{Context, ContextMessage, ModelId, Role, TextMessage};
    use pretty_assertions::assert_eq;

    use super::*;

    fn create_test_context(message: impl ToString) -> String {
        let context = Context {
            conversation_id: None,
            messages: message
                .to_string()
                .chars()
                .map(|c| match c {
                    's' => ContextMessage::Text(TextMessage {
                        role: Role::System,
                        content: c.to_string(),
                        tool_calls: None,
                        model: None,
                    }),
                    'u' => ContextMessage::Text(TextMessage {
                        role: Role::User,
                        content: c.to_string(),
                        tool_calls: None,
                        model: ModelId::new("gpt-4").into(),
                    }),
                    'a' => ContextMessage::Text(TextMessage {
                        role: Role::Assistant,
                        content: c.to_string(),
                        tool_calls: None,
                        model: None,
                    }),
                    _ => {
                        panic!("Invalid character in test message");
                    }
                })
                .collect(),
            tools: vec![],
            tool_choice: None,
            max_tokens: None,
            temperature: None,
            top_p: None,
            top_k: None,
            parallel_tool_calls: None,
        };

        let request = Request::from(context);
        let mut transformer = SetCache;
        let request = transformer.transform(request);
        let mut output = String::new();
        let sequences = request
            .messages
            .into_iter()
            .flatten()
            .flat_map(|m| m.content)
            .enumerate()
            .filter(|(_, m)| m.is_cached())
            .map(|(i, _)| i)
            .collect::<HashSet<usize>>();

        for (i, c) in message.to_string().chars().enumerate() {
            if sequences.contains(&i) {
                output.push('[');
            }
            output.push_str(c.to_string().as_str())
        }

        output
    }

    #[test]
    fn test_transformation() {
        let actual = create_test_context("suu");
        let expected = "suu";
        assert_eq!(actual, expected);

        let actual = create_test_context("suua");
        let expected = "suua";
        assert_eq!(actual, expected);

        let actual = create_test_context("suuau");
        let expected = "[suuau";
        assert_eq!(actual, expected);

        let actual = create_test_context("suuauu");
        let expected = "[suuauu";
        assert_eq!(actual, expected);

        let actual = create_test_context("suuauuaaau");
        let expected = "[s[uuauuaaau";
        assert_eq!(actual, expected);

        let actual = create_test_context("suuauuaaauauau");
        let expected = "suua[uuaaa[uauau";
        assert_eq!(actual, expected);
    }
}
