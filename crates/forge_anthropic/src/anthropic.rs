use anyhow::Context as _;
use derive_setters::Setters;
use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Parameters, ProviderService, ResultStream,
};
use reqwest::header::{HeaderMap, HeaderValue};
use reqwest::{Client, Url};
use reqwest_eventsource::{Event, RequestBuilderExt};
use tokio_stream::StreamExt;

use crate::request::Request;
use crate::response::ListModelResponse;

#[derive(Debug, Default, Clone, Setters)]
#[setters(into, strip_option)]
pub struct AnthropicBuilder {
    api_key: Option<String>,
    base_url: Option<String>,
    anthropic_version: Option<String>,
}

impl AnthropicBuilder {
    pub fn build(self) -> anyhow::Result<Anthropic> {
        let client = Client::builder().build()?;
        let base_url = self
            .base_url
            .as_deref()
            .unwrap_or("https://api.anthropic.com/v1/");

        let base_url = Url::parse(base_url)
            .with_context(|| format!("Failed to parse base URL: {}", base_url))?;
        let anthropic_version = self
            .anthropic_version
            .unwrap_or_else(|| "2023-06-01".to_string());

        Ok(Anthropic { client, base_url, api_key: self.api_key, anthropic_version })
    }
}

#[derive(Clone)]
pub struct Anthropic {
    client: Client,
    api_key: Option<String>,
    base_url: Url,
    anthropic_version: String,
}

impl Anthropic {
    pub fn builder() -> AnthropicBuilder {
        AnthropicBuilder::default()
    }

    fn url(&self, path: &str) -> anyhow::Result<Url> {
        // Validate the path doesn't contain certain patterns
        if path.contains("://") || path.contains("..") {
            anyhow::bail!("Invalid path: Contains forbidden patterns");
        }

        // Remove leading slash to avoid double slashes
        let path = path.trim_start_matches('/');

        self.base_url
            .join(path)
            .with_context(|| format!("Failed to append {} to base URL: {}", path, self.base_url))
    }

    fn headers(&self) -> HeaderMap {
        let mut headers = HeaderMap::new();

        // note: anthropic api requires the api key to be sent in `x-api-key` header.
        if let Some(ref api_key) = self.api_key {
            headers.insert("x-api-key", HeaderValue::from_str(api_key).unwrap());
        }

        // note: `anthropic-version` header is required by the API.
        headers.insert(
            "anthropic-version",
            HeaderValue::from_str(&self.anthropic_version).unwrap(),
        );
        headers.insert("X-Title", HeaderValue::from_static("code-forge"));
        headers
    }
}

#[async_trait::async_trait]
impl ProviderService for Anthropic {
    async fn chat(
        &self,
        id: &ModelId,
        context: Context,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        // TODO: depending on model, we've to set the max_tokens for request.
        let request = Request::from(context)
            .model(id.to_string())
            .stream(true)
            .max_tokens(4000u64);

        let es = self
            .client
            .post(self.url("/messages")?)
            .headers(self.headers())
            .json(&request)
            .eventsource()?;

        let stream = es
            .take_while(|message| !matches!(message, Err(reqwest_eventsource::Error::StreamEnded)))
            .then(|event| async {
                match event {
                    Ok(event) => match event {
                        Event::Open => None,
                        Event::Message(event) if ["[DONE]", ""].contains(&event.data.as_str()) => {
                            None
                        }
                        Event::Message(_event) => Some(
                            todo!(), /* serde_json::from_str::<OpenRouterResponse>(&event.data)
                                      *     .with_context(|| "Failed to parse OpenRouter
                                      * response")
                                      *     .and_then(|message| {
                                      *         ChatCompletionMessage::try_from(message.clone())
                                      *             .with_context(|| "Failed to create
                                      * completion message")
                                      *     }), */
                        ),
                    },
                    Err(reqwest_eventsource::Error::StreamEnded) => None,
                    // Err(reqwest_eventsource::Error::InvalidStatusCode(_, response)) => Some(
                    //     response
                    //         .json::<OpenRouterResponse>()
                    //         .await
                    //         .with_context(|| "Failed to parse OpenRouter response")
                    //         .and_then(|message| {
                    //             ChatCompletionMessage::try_from(message.clone())
                    //                 .with_context(|| "Failed to create completion message")
                    //         })
                    //         .with_context(|| "Failed with invalid status code"),
                    // ),
                    // Err(reqwest_eventsource::Error::InvalidContentType(_, response)) => Some(
                    //     response
                    //         .json::<OpenRouterResponse>()
                    //         .await
                    //         .with_context(|| "Failed to parse OpenRouter response")
                    //         .and_then(|message| {
                    //             ChatCompletionMessage::try_from(message.clone())
                    //                 .with_context(|| "Failed to create completion message")
                    //         })
                    //         .with_context(|| "Failed with invalid content type"),
                    // ),
                    Err(err) => Some(Err(err.into())),
                }
            });

        Ok(Box::pin(stream.filter_map(|x| x)))
    }
    async fn models(&self) -> anyhow::Result<Vec<Model>> {
        let text = self
            .client
            .get(self.url("models")?)
            .headers(self.headers())
            .send()
            .await?
            .error_for_status()
            .with_context(|| "Failed because of a non 200 status code".to_string())?
            .text()
            .await?;
        let response: ListModelResponse = serde_json::from_str(&text)?;
        Ok(response.data.into_iter().map(Into::into).collect())
    }
    async fn parameters(&self, _model: &ModelId) -> anyhow::Result<Parameters> {
        // note: didn't find any api docs for this endpoint.
        Ok(Parameters::default())
    }
}

#[cfg(test)]
mod tests {
    use forge_domain::{
        Context, ContextMessage, ToolCallFull, ToolCallId, ToolChoice, ToolName, ToolResult,
    };

    use crate::anthropic::Anthropic;
    use crate::request::Request;

    #[tokio::test]
    async fn test_url_for_models() {
        let anthropic = Anthropic::builder().api_key("sk-some-key").build().unwrap();
        assert_eq!(
            anthropic.url("/models").unwrap().as_str(),
            "https://api.anthropic.com/v1/models"
        );
    }

    #[tokio::test]
    async fn test_request_conversion() {
        let context = Context::default()
            .add_message(ContextMessage::system(
                "You're expert at math, so you should resolve all user queries.",
            ))
            .add_message(ContextMessage::user("what's 2 + 2 ?"))
            .add_message(ContextMessage::assistant(
                "here is the system call.",
                Some(vec![ToolCallFull {
                    name: ToolName::new("math"),
                    call_id: Some(ToolCallId::new("math-1")),
                    arguments: serde_json::json!({"expression": "2 + 2"}),
                }]),
            ))
            .add_tool_results(vec![ToolResult {
                name: ToolName::new("math"),
                call_id: Some(ToolCallId::new("math-1")),
                content: serde_json::json!({"result": 4}).to_string(),
                is_error: false,
            }])
            .tool_choice(ToolChoice::Call(ToolName::new("math")));
        let request = Request::from(context)
            .model("sonnet-3.5".to_string())
            .stream(true)
            .max_tokens(4000u64);
        insta::assert_snapshot!(serde_json::to_string_pretty(&request).unwrap());
    }
}
