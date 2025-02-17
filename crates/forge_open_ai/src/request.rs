use async_openai::types::{
    ChatCompletionNamedToolChoice, ChatCompletionTool, ChatCompletionToolChoiceOption,
    ChatCompletionToolType, CreateChatCompletionRequest, FunctionName, FunctionObject,
};
use forge_domain::{Context, ToolChoice, ToolDefinition};

use crate::lift::{Lift, LiftUp};

impl From<Context> for Lift<CreateChatCompletionRequest> {
    fn from(context: Context) -> Self {
        let mut request = CreateChatCompletionRequest::default();
        request.tool_choice = context
            .tool_choice
            .map(|tool_choice| Lift::from(tool_choice).take());

        request.tools = Some(
            context
                .tools
                .into_iter()
                .map(|tool| Lift::from(tool).take())
                .collect(),
        );
        request.lift()
    }
}

impl From<ToolChoice> for Lift<ChatCompletionToolChoiceOption> {
    fn from(value: ToolChoice) -> Self {
        match value {
            ToolChoice::Auto => ChatCompletionToolChoiceOption::Auto,
            ToolChoice::None => ChatCompletionToolChoiceOption::None,
            ToolChoice::Required => ChatCompletionToolChoiceOption::Required,
            ToolChoice::Call(_tool) => {
                ChatCompletionToolChoiceOption::Named(ChatCompletionNamedToolChoice {
                    r#type: ChatCompletionToolType::Function,
                    function: FunctionName { name: _tool.into_string() },
                })
            }
        }
        .lift()
    }
}

impl From<ToolDefinition> for Lift<ChatCompletionTool> {
    fn from(tool: ToolDefinition) -> Self {
        ChatCompletionTool {
            r#type: ChatCompletionToolType::Function,
            function: FunctionObject {
                name: tool.name.into_string(),
                description: Some(tool.description),
                parameters: serde_json::to_value(tool.input_schema).ok(),
                strict: None,
            },
        }
        .lift()
    }
}
