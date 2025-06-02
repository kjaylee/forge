use crate::forge_provider::request::Request;
use crate::forge_provider::transformers::Transformer;

/// Transformer that enables parallel tool calls.
pub struct ParallelToolCall;

impl Transformer for ParallelToolCall {
    fn transform(&self, mut request: Request) -> Request {
        if request
            .tools
            .as_ref()
            .map_or(false, |tools| !tools.is_empty())
        {
            request.parallel_tool_calls = Some(true);
        }
        request
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forge_provider::request::{Tool, FunctionDescription};
    use crate::forge_provider::tool_choice::FunctionType;
    use serde_json::json;

    #[test]
    fn test_transform_with_tools() {
        let transformer = ParallelToolCall;
        let request = Request {
            tools: Some(vec![Tool {
                r#type: FunctionType,
                function: FunctionDescription {
                    name: "tool1".to_string(),
                    description: Some("test tool".to_string()),
                    parameters: json!({}),
                },
            }]),
            parallel_tool_calls: None,
            ..Default::default()
        };

        let transformed = transformer.transform(request);
        assert_eq!(transformed.parallel_tool_calls, Some(true));
    }

    #[test]
    fn test_transform_with_empty_tools() {
        let transformer = ParallelToolCall;
        let request = Request {
            tools: Some(vec![]),
            parallel_tool_calls: None,
            ..Default::default()
        };

        let transformed = transformer.transform(request);
        assert_eq!(transformed.parallel_tool_calls, None);
    }

    #[test]
    fn test_transform_with_no_tools() {
        let transformer = ParallelToolCall;
        let request = Request {
            tools: None,
            parallel_tool_calls: None,
            ..Default::default()
        };

        let transformed = transformer.transform(request);
        assert_eq!(transformed.parallel_tool_calls, None);
    }
}
