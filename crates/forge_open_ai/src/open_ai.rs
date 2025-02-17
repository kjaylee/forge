use anyhow::Context as _;
use async_openai::{config::OpenAIConfig, Client};
use forge_domain::{
    ChatCompletionMessage, Content, Context, Model, ModelId, Parameters, ProviderService,
    ResultStream, ToolCallId, ToolCallPart, ToolName,
};
use futures_util::StreamExt;

use crate::lift::Lift;

pub struct OpenAiBuilder {
    api_key: String,
}

impl OpenAiBuilder {
    pub fn new<S: Into<String>>(api_key: S) -> OpenAiBuilder {
        OpenAiBuilder { api_key: api_key.into() }
    }
    fn build(self) -> OpenAi {
        let config = OpenAIConfig::new().with_api_key(self.api_key);
        OpenAi { client: Client::with_config(config) }
    }
}

pub struct OpenAi {
    client: Client<OpenAIConfig>,
}

#[async_trait::async_trait]
impl ProviderService for OpenAi {
    async fn chat(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        let mut request = Lift::from(context).take();
        request.model = id.to_string();
        request.stream = Some(true);

        let response = self.client.chat().create_stream(request).await?;

        let stream = response
            .map(move |chunk_result| {
                chunk_result
                    .map(|chunk| {
                        if let Some(choice) = chunk.choices.into_iter().next() {
                            let mut completion_message = ChatCompletionMessage::assistant(
                                Content::part(choice.delta.content.unwrap_or_default()),
                            )
                            .finish_reason_opt(
                                choice.finish_reason.map(|reason| Lift::from(reason).take()),
                            );

                            // Handle tool calls if present
                            if let Some(tool_calls) = choice.delta.tool_calls {
                                for tool_call in tool_calls {
                                    if let Some(function) = tool_call.function {
                                        completion_message =
                                            completion_message.add_tool_call(ToolCallPart {
                                                call_id: tool_call.id.map(ToolCallId::new),
                                                name: function.name.map(ToolName::new),
                                                arguments_part: function
                                                    .arguments
                                                    .unwrap_or_default(),
                                            });
                                    }
                                }
                            }

                            // Handle usage information if present
                            if let Some(usage) = chunk.usage {
                                completion_message =
                                    completion_message.usage(Lift::from(usage).take());
                            }

                            completion_message
                        } else {
                            ChatCompletionMessage::assistant(Content::part("".to_string()))
                        }
                    })
                    .context("Failed to process chat completion chunk")
            })
            .boxed();

        Ok(Box::pin(stream))
    }

    async fn models(&self) -> anyhow::Result<Vec<Model>> {
        Ok(self
            .client
            .models()
            .list()
            .await?
            .data
            .into_iter()
            .map(|model| Lift::<Model>::from(model).take())
            .collect::<Vec<_>>())
    }

    async fn parameters(&self, _model: &ModelId) -> anyhow::Result<Parameters> {
        // note: Open-ai: doesn't provide capability to access parameters of model via some api.
        Ok(Parameters::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_models() {
        let open_ai = OpenAiBuilder::new("test-key").build();
        let models = open_ai.models().await.unwrap();
        assert!(!models.is_empty());
    }
}
