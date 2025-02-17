use forge_domain::{FinishReason, Model, ModelId, Usage};

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
