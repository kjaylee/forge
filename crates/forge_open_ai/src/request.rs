use async_openai::types::{
    ChatCompletionMessageToolCall, ChatCompletionNamedToolChoice,
    ChatCompletionRequestAssistantMessage, ChatCompletionRequestAssistantMessageContent,
    ChatCompletionRequestMessage, ChatCompletionRequestSystemMessage,
    ChatCompletionRequestSystemMessageContent, ChatCompletionRequestToolMessage,
    ChatCompletionRequestToolMessageContent, ChatCompletionRequestUserMessage,
    ChatCompletionRequestUserMessageContent, ChatCompletionTool, ChatCompletionToolChoiceOption,
    ChatCompletionToolType, CreateChatCompletionRequest, FunctionCall, FunctionName,
    FunctionObject,
};
use forge_domain::{Context, ContextMessage, ToolCallFull, ToolChoice, ToolDefinition};

use crate::lift::{Lift, LiftUp};

impl From<Context> for Lift<CreateChatCompletionRequest> {
    fn from(context: Context) -> Self {
        CreateChatCompletionRequest {
            tool_choice: context
                .tool_choice
                .map(|tool_choice| Lift::from(tool_choice).take()),
            tools: Some(
                context
                    .tools
                    .into_iter()
                    .map(|tool| Lift::from(tool).take())
                    .collect(),
            ),
            messages: context
                .messages
                .into_iter()
                .map(|message| Lift::from(message).take())
                .collect(),
            parallel_tool_calls: Some(false),
            ..Default::default()
        }
        .lift()
    }
}

impl From<ContextMessage> for Lift<ChatCompletionRequestMessage> {
    fn from(value: ContextMessage) -> Self {
        match value {
            ContextMessage::ContentMessage(chat_message) => match chat_message.role {
                forge_domain::Role::Assistant => {
                    ChatCompletionRequestMessage::Assistant(ChatCompletionRequestAssistantMessage {
                        content: Some(ChatCompletionRequestAssistantMessageContent::Text(
                            chat_message.content,
                        )),
                        refusal: None,
                        name: None,
                        audio: None,
                        tool_calls: chat_message.tool_calls.map(|tool_calls| {
                            tool_calls
                                .into_iter()
                                .map(|tc| Lift::from(tc).take())
                                .collect::<Vec<_>>()
                        }),
                        function_call: None,
                    })
                }
                forge_domain::Role::User => {
                    ChatCompletionRequestMessage::User(ChatCompletionRequestUserMessage {
                        content: ChatCompletionRequestUserMessageContent::Text(
                            chat_message.content,
                        ),
                        name: None,
                    })
                }
                forge_domain::Role::System => {
                    ChatCompletionRequestMessage::System(ChatCompletionRequestSystemMessage {
                        content: ChatCompletionRequestSystemMessageContent::Text(
                            chat_message.content,
                        ),
                        name: None,
                    })
                }
            },
            ContextMessage::ToolMessage(tool_result) => {
                let call_id = tool_result.call_id.as_ref().unwrap();
                ChatCompletionRequestMessage::Tool(ChatCompletionRequestToolMessage {
                    tool_call_id: call_id.as_str().to_string(),
                    content: ChatCompletionRequestToolMessageContent::Text(tool_result.content),
                })
            }
        }
        .lift()
    }
}

impl From<ToolCallFull> for Lift<ChatCompletionMessageToolCall> {
    fn from(value: ToolCallFull) -> Self {
        let id = value.call_id.as_ref().unwrap();
        ChatCompletionMessageToolCall {
            id: id.as_str().to_string(),
            r#type: ChatCompletionToolType::Function,
            function: FunctionCall {
                name: value.name.into_string(),
                arguments: serde_json::to_string(&value.arguments).unwrap(),
            },
        }
        .lift()
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
