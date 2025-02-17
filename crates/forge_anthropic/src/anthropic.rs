use anyhow::Context as _;
use derive_setters::Setters;
use forge_domain::{
    ChatCompletionMessage, Context, Model, ModelId, Parameters, ProviderService, ResultStream,
};
use reqwest::{
    header::{HeaderMap, HeaderValue},
    Client, Url,
};

use crate::{request::Request, response::ListModelResponse};

#[derive(Debug, Default, Clone, Setters)]
pub struct AnthropicBuilder {
    api_key: Option<String>,
    base_url: Option<String>,
}

impl AnthropicBuilder {
    pub fn build(self) -> anyhow::Result<Anthropic> {
        let client = Client::builder().build()?;
        let base_url = self
            .base_url
            .as_deref()
            .unwrap_or("https://api.anthropic.com/v1");

        let base_url = Url::parse(base_url)
            .with_context(|| format!("Failed to parse base URL: {}", base_url))?;

        Ok(Anthropic { client, base_url, api_key: self.api_key })
    }
}

#[derive(Clone)]
pub struct Anthropic {
    client: Client,
    api_key: Option<String>,
    base_url: Url,
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
            headers.insert("x-api-key", HeaderValue::from_str(&api_key).unwrap());
        }

        // note: `anthropic-version` header is required by the API.
        headers.insert("anthropic-version", HeaderValue::from_static("2023-06-01"));
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
        let request = Request::from(context).model(id.to_string()).stream(true);

        todo!()
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
