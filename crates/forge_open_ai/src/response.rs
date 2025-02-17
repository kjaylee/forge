use async_openai::types::CreateChatCompletionStreamResponse;
use forge_domain::{
    ChatCompletionMessage, Content, FinishReason, Model, ModelId, ToolCallId, ToolCallPart,
    ToolName, Usage,
};

use crate::lift::{Lift, LiftUp};

impl From<async_openai::types::Model> for Lift<Model> {
    fn from(model: async_openai::types::Model) -> Self {
        Model {
            id: ModelId::new(&model.id),
            name: model.id,
            description: None,
            context_length: None,
        }
        .lift()
    }
}

impl From<async_openai::types::FinishReason> for Lift<FinishReason> {
    fn from(reason: async_openai::types::FinishReason) -> Self {
        match reason {
            async_openai::types::FinishReason::ContentFilter => FinishReason::ContentFilter,
            async_openai::types::FinishReason::Length => FinishReason::Length,
            async_openai::types::FinishReason::FunctionCall => {
                todo!("not sure what's this")
            }
            async_openai::types::FinishReason::Stop => FinishReason::Stop,
            async_openai::types::FinishReason::ToolCalls => FinishReason::ToolCalls,
        }
        .lift()
    }
}

impl From<async_openai::types::CompletionUsage> for Lift<Usage> {
    fn from(usage: async_openai::types::CompletionUsage) -> Self {
        Usage {
            prompt_tokens: usage.prompt_tokens as u64,
            completion_tokens: usage.completion_tokens as u64,
            total_tokens: usage.total_tokens as u64,
        }
        .lift()
    }
}

impl From<CreateChatCompletionStreamResponse> for Lift<ChatCompletionMessage> {
    fn from(chunk: CreateChatCompletionStreamResponse) -> Self {
        if let Some(choice) = chunk.choices.into_iter().next() {
            let mut completion_message = ChatCompletionMessage::assistant(Content::part(
                choice.delta.content.unwrap_or_default(),
            ))
            .finish_reason_opt(choice.finish_reason.map(|reason| Lift::from(reason).take()));

            // Handle tool calls if present
            if let Some(tool_calls) = choice.delta.tool_calls {
                for tool_call in tool_calls {
                    if let Some(function) = tool_call.function {
                        completion_message = completion_message.add_tool_call(ToolCallPart {
                            call_id: tool_call.id.map(ToolCallId::new),
                            name: function.name.map(ToolName::new),
                            arguments_part: function.arguments.unwrap_or_default(),
                        });
                    }
                }
            }

            // Handle usage information if present
            if let Some(usage) = chunk.usage {
                completion_message = completion_message.usage(Lift::from(usage).take());
            }

            completion_message
        } else {
            // TODO: raise empty content error
            ChatCompletionMessage::assistant(Content::part("".to_string()))
        }
        .lift()
    }
}
