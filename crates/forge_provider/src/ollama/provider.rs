use std::pin::Pin;

use async_trait::async_trait;
use forge_domain::{ChatCompletionMessage, Context, Model, ModelId, Parameters, ResultStream};
use futures::{Stream, StreamExt};
use reqwest::Client;
use reqwest_eventsource::{Event, EventSource};

use super::request::ChatRequest;
use super::response::{ChatResponse, ModelsResponse};
use crate::error::Error;
use crate::provider::ProviderService;

const DEFAULT_BASE_URL: &str = "http://localhost:11434/api/v1";

#[derive(Debug, Clone)]
pub struct Config {
    pub base_url: String,
}

impl Default for Config {
    fn default() -> Self {
        Self { base_url: DEFAULT_BASE_URL.to_string() }
    }
}

pub struct Ollama {
    client: Client,
    config: Config,
}

impl Ollama {
    pub fn new(config: Config) -> Self {
        Self { client: Client::new(), config }
    }

    fn chat_url(&self) -> String {
        format!("{}/chat", self.config.base_url)
    }

    fn models_url(&self) -> String {
        format!("{}/tags", self.config.base_url)
    }
}

#[async_trait]
impl ProviderService for Ollama {
    async fn chat(&self, context: Context) -> ResultStream<ChatCompletionMessage, Error> {
        let mut request = ChatRequest::try_from(context).map_err(|_| Error::EmptyContent)?;
        let url = self.chat_url();
        request.stream = true;

        println!(
            "Request: {}",
            serde_json::to_string_pretty(&request).unwrap()
        );

        let client = reqwest::Client::new();
        let request_builder = client
            .post(&url)
            .header("Content-Type", "application/json")
            .json(&request);

        let es = EventSource::new(request_builder).map_err(Error::from)?;

        let stream = es.filter_map(|event| async move {
            match event {
                Ok(Event::Message(message)) => Some(
                    serde_json::from_str::<ChatResponse>(&message.data)
                        .map_err(Error::from)
                        .and_then(|resp| {
                            ChatCompletionMessage::try_from(resp).map_err(|_| Error::EmptyContent)
                        }),
                ),
                Ok(Event::Open) => None,
                Err(e) => Some(Err(Error::EventSource(e))),
            }
        });

        Ok(Box::pin(stream)
            as Pin<
                Box<dyn Stream<Item = Result<ChatCompletionMessage, Error>> + Send>,
            >)
    }

    async fn models(&self) -> Result<Vec<Model>, Error> {
        let response = self
            .client
            .get(self.models_url())
            .send()
            .await?
            .json::<ModelsResponse>()
            .await?;

        Ok(response
            .models
            .into_iter()
            .map(|model| Model {
                id: model.name.clone(),
                name: model.name.as_str().to_string(),
                description: None,
            })
            .collect())
    }

    async fn parameters(&self, _model: &ModelId) -> Result<Parameters, Error> {
        // Ollama has simple parameter set that's same for all models
        Ok(Parameters::new(true))
    }
}
