use crate::request::{OpenRouterRequest, OpenRouterRole};
use crate::transformers::Transformer;

/// Converts tool call messages to user messages
pub struct ConvertToolCalls;

impl Transformer for ConvertToolCalls {
    fn transform(&self, mut request: OpenRouterRequest) -> OpenRouterRequest {
        if let Some(messages) = request.messages.as_mut() {
            for message in messages.iter_mut() {
                // Convert tool messages to user messages
                if message.role == OpenRouterRole::Tool {
                    message.role = OpenRouterRole::User;
                    message.tool_calls = None;
                    message.tool_call_id = None;
                    message.name = None;
                }
                // Remove tool calls from assistant messages
                if message.role == OpenRouterRole::Assistant {
                    message.tool_calls = None;
                }
            }
        }

        request
    }
}

#[cfg(test)]
mod tests {
    use forge_domain::{
        ContentMessage, Context, ContextMessage, Role, ToolCallFull, ToolCallId, ToolName,
        ToolResult,
    };
    use serde_json::json;

    use super::*;

    #[test]
    fn test_mistral_transformer_tools_not_supported() {
        let tool_call = ToolCallFull {
            call_id: Some(ToolCallId::new("123")),
            name: ToolName::new("test_tool"),
            arguments: json!({"key": "value"}),
        };

        let tool_result = ToolResult::new(ToolName::new("test_tool"))
            .call_id(ToolCallId::new("123"))
            .success("test result");

        let context = Context {
            messages: vec![
                ContextMessage::ContentMessage(ContentMessage {
                    role: Role::Assistant,
                    content: "Using tool".to_string(),
                    tool_calls: Some(vec![tool_call]),
                }),
                ContextMessage::ToolMessage(tool_result),
            ],
            tools: vec![],
            tool_choice: None,
        };

        let request = OpenRouterRequest::from(context);
        let transformer = ConvertToolCalls;
        let transformed = transformer.transform(request);

        let messages = transformed.messages.unwrap();
        assert!(messages[0].tool_calls.is_none()); // Assistant message
        assert_eq!(messages[1].role, OpenRouterRole::User); // Converted tool
                                                            // message
    }

    #[test]
    fn test_mistral_transformer_tools_supported() {
        let tool_call = ToolCallFull {
            call_id: Some(ToolCallId::new("123")),
            name: ToolName::new("test_tool"),
            arguments: json!({"key": "value"}),
        };

        let tool_result = ToolResult::new(ToolName::new("test_tool"))
            .call_id(ToolCallId::new("123"))
            .success("test result");

        let context = Context {
            messages: vec![
                ContextMessage::ContentMessage(ContentMessage {
                    role: Role::Assistant,
                    content: "Using tool".to_string(),
                    tool_calls: Some(vec![tool_call]),
                }),
                ContextMessage::ToolMessage(tool_result),
            ],
            tools: vec![],
            tool_choice: None,
        };

        let request = OpenRouterRequest::from(context);
        let transformer = ConvertToolCalls;
        let transformed = transformer.transform(request);

        let messages = transformed.messages.unwrap();
        assert!(messages[0].tool_calls.is_some()); // Assistant message keeps tool calls
        assert_eq!(messages[1].role, OpenRouterRole::Tool); // Tool message
                                                            // remains as tool
    }
}
