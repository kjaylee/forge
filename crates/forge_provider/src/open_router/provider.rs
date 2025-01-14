use forge_domain::{ChatCompletionMessage, Context, Model, ModelId, Parameters, ResultStream};
use reqwest::header::{HeaderMap, HeaderValue, AUTHORIZATION};
use reqwest::Client;
use reqwest_eventsource::{Event, EventSource};
use tokio_stream::StreamExt;

use super::model::{ListModelResponse, OpenRouterModel};
use super::request::OpenRouterRequest;
use super::response::OpenRouterResponse;
use super::ParameterResponse;
use crate::error::Result;
use crate::provider::ProviderService;
use crate::{Error, Live, Service};

#[derive(Debug, Clone)]
struct Config {
    api_key: String,
}

impl Config {
    fn api_base(&self) -> &str {
        "https://openrouter.ai/api/v1"
    }

    fn headers(&self) -> HeaderMap {
        let mut headers = HeaderMap::new();
        headers.insert(
            AUTHORIZATION,
            HeaderValue::from_str(&format!("Bearer {}", self.api_key)).unwrap(),
        );
        headers.insert("X-Title", HeaderValue::from_static("Code Forge"));
        headers
    }

    fn url(&self, path: &str) -> String {
        format!("{}{}", self.api_base(), path)
    }
}

#[derive(Clone)]
struct OpenRouter {
    client: Client,
    config: Config,
}

impl OpenRouter {
    fn new(api_key: impl ToString) -> Self {
        let config = Config { api_key: api_key.to_string() };

        let client = Client::builder().build().unwrap();

        Self { client, config }
    }
}

#[async_trait::async_trait]
impl ProviderService for OpenRouter {
    async fn chat(&self, request: Context) -> ResultStream<ChatCompletionMessage, Error> {
        let mut request = OpenRouterRequest::from(request);
        request.stream = Some(true);
        let request = serde_json::to_string(&request)?;

        let rb = self
            .client
            .post(self.config.url("/chat/completions"))
            .headers(self.config.headers())
            .body(request);

        let es = EventSource::new(rb).unwrap();

        let stream = es
            .filter_map(|event| match event {
                Ok(ref event) => match event {
                    Event::Open => None,
                    Event::Message(event) => {
                        // Ignoring wasteful events
                        if ["[DONE]", ""].contains(&event.data.as_str()) {
                            return None;
                        }

                        let message = serde_json::from_str::<OpenRouterResponse>(&event.data)
                            .map_err(Error::from)
                            .and_then(|message| ChatCompletionMessage::try_from(message.clone()));

                        Some(message)
                    }
                },
                Err(err) => Some(Err(err.into())),
            })
            .take_while(|message| {
                !matches!(
                    message,
                    Err(Error::EventSource(reqwest_eventsource::Error::StreamEnded))
                )
            });

        Ok(Box::pin(Box::new(stream)))
    }

    async fn models(&self) -> Result<Vec<Model>> {
        let text = self
            .client
            .get(self.config.url("/models"))
            .headers(self.config.headers())
            .send()
            .await?
            .error_for_status()?
            .text()
            .await?;

        let response: ListModelResponse = serde_json::from_str(&text)?;

        Ok(response
            .data
            .iter()
            .map(|r| r.clone().into())
            .collect::<Vec<Model>>())
    }

    async fn parameters(&self, model: &ModelId) -> Result<Parameters> {
        // https://openrouter.ai/api/v1/parameters/google/gemini-pro-1.5-exp
        let path = format!("/parameters/{}", model.as_str());
        let text = self
            .client
            .get(self.config.url(&path))
            .headers(self.config.headers())
            .send()
            .await?
            .error_for_status()?
            .text()
            .await?;

        let response: ParameterResponse = serde_json::from_str(&text)?;

        Ok(Parameters {
            tool_supported: response
                .data
                .supported_parameters
                .iter()
                .flat_map(|parameter| parameter.iter())
                .any(|parameter| parameter == "tools"),
        })
    }
}

impl Service {
    pub fn open_router(api_key: impl ToString) -> impl ProviderService {
        Live::new(OpenRouter::new(api_key))
    }
}

impl From<OpenRouterModel> for Model {
    fn from(value: OpenRouterModel) -> Self {
        Model {
            id: value.id,
            name: value.name,
            description: value.description,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_router::response::MetaDataError;

    #[test]
    fn test_error_without_metadata() {
        let content = serde_json::to_string(&serde_json::json!({
          "error": {
            "message": "This endpoint's maximum context length is 16384 tokens",
            "code": 400
          }
        }))
        .unwrap();
        let message = serde_json::from_str::<OpenRouterResponse>(&content)
            .map_err(Error::from)
            .and_then(|message| ChatCompletionMessage::try_from(message.clone()));

        assert!(matches!(message, Err(Error::Upstream { .. })));
        if let Err(Error::Upstream { message, code, metadata }) = message {
            assert_eq!(
                message,
                "This endpoint's maximum context length is 16384 tokens"
            );
            assert_eq!(code, 400);
            assert!(metadata.is_none());
        }
    }

    #[test]
    fn test_error_with_metadata_provider_error() {
        let content = serde_json::to_string(&serde_json::json!({
          "error": {
            "message": "This endpoint's maximum context length is 16384 tokens",
            "code": 400,
            "metadata": {
                "provider_name": "OpenAI",
                "raw": {
                    "__kind": "OK",
                    "data": "{\n  \"error\": {\n    \"message\": \"Invalid 'tools[4].function.description': string too long. Expected a string with maximum length 1024, but got a string with length 1392 instead.\",\n    \"type\": \"invalid_request_error\",\n    \"param\": \"tools[4].function.description\",\n    \"code\": \"string_above_max_length\"\n  }\n}"
                }
            }
          }
        }))
        .unwrap();
        let message = serde_json::from_str::<OpenRouterResponse>(&content)
            .map_err(Error::from)
            .and_then(|message| ChatCompletionMessage::try_from(message.clone()));

        assert!(matches!(message, Err(Error::Upstream { .. })));
        if let Err(Error::Upstream { message, code, metadata }) = message {
            assert_eq!(
                message,
                "This endpoint's maximum context length is 16384 tokens"
            );
            assert_eq!(code, 400);
            assert!(metadata.is_some());
            let provider_error =
                serde_json::from_value::<MetaDataError>(metadata.unwrap()).unwrap();
            assert!(matches!(provider_error, MetaDataError::Provider { .. }));
        }
    }

    #[test]
    fn test_error_with_metadata_moderation_error() {
        let content = serde_json::to_string(&serde_json::json!({
            "error": {
                "message": "Your input was flagged for moderation.",
                "code": 403,
                "metadata": {
                    "type": "moderation",
                    "reasons": ["offensive_language"],
                    "flagged_input": "This is flagged text...",
                    "provider_name": "OpenAI",
                    "model_slug": "gpt-4"
                }
            }
        }))
        .unwrap();
        let message = serde_json::from_str::<OpenRouterResponse>(&content)
            .map_err(Error::from)
            .and_then(|message| ChatCompletionMessage::try_from(message.clone()));

        assert!(matches!(message, Err(Error::Upstream { .. })));
        if let Err(Error::Upstream { message, code, metadata }) = message {
            assert_eq!(message, "Your input was flagged for moderation.");
            assert_eq!(code, 403);
            assert!(metadata.is_some());
            let moderation_error =
                serde_json::from_value::<MetaDataError>(metadata.unwrap()).unwrap();
            assert!(matches!(moderation_error, MetaDataError::Moderation { .. }));
        }
    }

    #[test]
    fn test_error_with_metadata_other_error() {
        let content = serde_json::to_string(&serde_json::json!({
            "error": {
                "message": "Credits ran out.",
                "code": 402,
                "metadata": {
                    "failure": "Credits ran out"
                }
            }
        }))
        .unwrap();
        let message = serde_json::from_str::<OpenRouterResponse>(&content)
            .map_err(Error::from)
            .and_then(|message| ChatCompletionMessage::try_from(message.clone()));

        assert!(matches!(message, Err(Error::Upstream { .. })));
        if let Err(Error::Upstream { message, code, metadata }) = message {
            assert_eq!(message, "Credits ran out.");
            assert_eq!(code, 402);
            assert!(metadata.is_some());
            let moderation_error =
                serde_json::from_value::<MetaDataError>(metadata.unwrap()).unwrap();
            assert!(matches!(moderation_error, MetaDataError::Other { .. }));
        }
    }
}
