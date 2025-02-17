#![allow(dead_code)]
use async_openai::config::OpenAIConfig;
use async_openai::Client;
use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Parameters, ProviderService, ResultStream,
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
            .map(move |chunk_result| match chunk_result {
                Ok(chunk) => Ok(Lift::from(chunk).take()),
                Err(err) => Err(err.into()),
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
        // note: Open-ai: doesn't provide capability to access parameters of model via
        // api.
        Ok(Parameters::default())
    }
}
