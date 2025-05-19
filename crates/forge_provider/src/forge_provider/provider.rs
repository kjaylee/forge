use std::sync::Arc;

use anyhow::{Context as _, Result};
use derive_builder::Builder;
use forge_domain::{
    self, ChatCompletionMessage, Compact, Context as ChatContext, ModelId, Provider,
    ProviderService, ResultStream, TemplateService,
};
use reqwest::header::{HeaderMap, HeaderValue, AUTHORIZATION};
use reqwest::{Client, Url};
use reqwest_eventsource::{Event, RequestBuilderExt};
use tokio_stream::StreamExt;
use tracing::debug;

use super::model::{ListModelResponse, Model};
use super::request::Request;
use super::response::Response;
use crate::compaction::ForgeCompactionService;
use crate::forge_provider::transformers::{ProviderPipeline, Transformer};
use crate::utils::format_http_context;

#[derive(Clone, Builder)]
pub struct ForgeProvider<T: Clone> {
    client: Client,
    provider: Provider,
    template_service: Option<Arc<T>>,
}

impl<T: TemplateService + Clone> ForgeProvider<T> {
    pub fn builder() -> ForgeProviderBuilder<T> {
        ForgeProviderBuilder::default()
    }

    fn url(&self, path: &str) -> anyhow::Result<Url> {
        // Validate the path doesn't contain certain patterns
        if path.contains("://") || path.contains("..") {
            anyhow::bail!("Invalid path: Contains forbidden patterns");
        }

        // Remove leading slash to avoid double slashes
        let path = path.trim_start_matches('/');

        self.provider.to_base_url().join(path).with_context(|| {
            format!(
                "Failed to append {} to base URL: {}",
                path,
                self.provider.to_base_url()
            )
        })
    }

    fn headers(&self) -> HeaderMap {
        let mut headers = HeaderMap::new();
        if let Some(ref api_key) = self.provider.key() {
            headers.insert(
                AUTHORIZATION,
                HeaderValue::from_str(&format!("Bearer {api_key}")).unwrap(),
            );
        }
        headers.insert("X-Title", HeaderValue::from_static("forge"));
        headers.insert(
            "HTTP-Referer",
            HeaderValue::from_static("https://github.com/antinomyhq/forge"),
        );
        headers.insert(
            reqwest::header::CONNECTION,
            HeaderValue::from_static("keep-alive"),
        );
        headers
    }

    async fn inner_chat(
        &self,
        model: &ModelId,
        context: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        let mut request = Request::from(context).model(model.clone()).stream(true);
        request = ProviderPipeline::new(&self.provider).transform(request);

        let url = self.url("chat/completions")?;

        debug!(
            url = %url,
            model = %model,
            message_count = %request.message_count(),
            message_cache_count = %request.message_cache_count(),
            "Connecting Upstream"
        );

        let es = self
            .client
            .post(url.clone())
            .headers(self.headers())
            .json(&request)
            .eventsource()
            .context(format_http_context(None, "POST", &url))?;

        let stream = es
            .take_while(|message| !matches!(message, Err(reqwest_eventsource::Error::StreamEnded)))
            .then(|event| async {
                match event {
                    Ok(event) => match event {
                        Event::Open => None,
                        Event::Message(event) if ["[DONE]", ""].contains(&event.data.as_str()) => {
                            debug!("Received completion from Upstream");
                            None
                        }
                        Event::Message(message) => Some(
                            serde_json::from_str::<Response>(&message.data)
                                .with_context(|| format!("Failed to parse Forge Provider response: {}", message.data))
                                .and_then(|event| {
                                    ChatCompletionMessage::try_from(event.clone())
                                        .with_context(|| format!("Failed to create completion message: {}", message.data))
                                }),
                        ),
                    },
                    Err(error) => match error {
                        reqwest_eventsource::Error::StreamEnded => None,
                        reqwest_eventsource::Error::InvalidStatusCode(_, response) => {
                            let headers = response.headers().clone();
                            let status = response.status();
                            match response.text().await {
                                Ok(ref body) => {
                                    debug!(status = ?status, headers = ?headers, body = body, "Invalid status code");
                                    Some(Err(anyhow::anyhow!("Invalid status code: {} Reason: {}", status, body)))
                                }
                                Err(error) => {
                                    debug!(status = ?status, headers = ?headers, body = ?error, "Invalid status code (body not available)");
                                    Some(Err(anyhow::anyhow!("Invalid status code: {}", status)))
                                }
                            }
                        }
                        reqwest_eventsource::Error::InvalidContentType(_, ref response) => {
                            let status_code = response.status();
                            debug!(response = ?response, "Invalid content type");
                            Some(Err(anyhow::anyhow!(error).context(format!("Http Status: {status_code}" ))))

                        }
                        error => {
                            debug!(error = %error, "Failed to receive chat completion event");
                            Some(Err(error.into()))
                        }
                    },
                }
            }).map(move |response| {
                match response {
                    Some(Err(err)) => Some(Err(anyhow::anyhow!(err).context(format_http_context(None, "POST", &url)))),
                    _ => response,
                }
            });

        Ok(Box::pin(stream.filter_map(|x| x)))
    }

    async fn inner_models(&self) -> Result<Vec<forge_domain::Model>> {
        let url = self.url("models")?;
        debug!(url = %url, "Fetching models");
        match self.fetch_models(url.clone()).await {
            Err(err) => {
                debug!(error = %err, "Failed to fetch models");
                anyhow::bail!(err)
            }
            Ok(response) => {
                let data: ListModelResponse = serde_json::from_str(&response)
                    .context(format_http_context(None, "GET", &url))
                    .context("Failed to deserialize models response")?;
                Ok(data.data.into_iter().map(Into::into).collect())
            }
        }
    }

    async fn fetch_models(&self, url: Url) -> Result<String, anyhow::Error> {
        match self
            .client
            .get(url.clone())
            .headers(self.headers())
            .send()
            .await
        {
            Ok(response) => {
                let ctx_message = format_http_context(Some(response.status()), "GET", &url);
                match response.error_for_status() {
                    Ok(response) => Ok(response
                        .text()
                        .await
                        .context(ctx_message)
                        .context("Failed to decode response into text")?),
                    Err(err) => Err(anyhow::anyhow!(err)
                        .context(ctx_message)
                        .context("Failed because of a non 200 status code")),
                }
            }
            Err(err) => {
                let ctx_msg = format_http_context(err.status(), "GET", &url);
                Err(anyhow::anyhow!(err)
                    .context(ctx_msg)
                    .context("Failed to fetch the models"))
            }
        }
    }
}

#[async_trait::async_trait]
impl<T: TemplateService + Clone + 'static> ProviderService for ForgeProvider<T> {
    async fn chat(
        &self,
        model: &ModelId,
        context: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        self.inner_chat(model, context).await
    }

    async fn models(&self) -> Result<Vec<forge_domain::Model>> {
        self.inner_models().await
    }

    async fn compact(
        &self,
        context: ChatContext,
        options: &Compact,
    ) -> anyhow::Result<ChatContext> {
        let compaction_service = ForgeCompactionService::new(
            self.template_service.clone().unwrap(),
            Arc::new(self.clone()),
        );
        compaction_service.compact_context(options, context).await
    }
}

impl From<Model> for forge_domain::Model {
    fn from(value: Model) -> Self {
        forge_domain::Model {
            id: value.id,
            name: value.name,
            description: value.description,
            context_length: value.context_length,
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;

    use super::*;

    #[test]
    fn test_error_deserialization() -> Result<()> {
        let content = serde_json::to_string(&serde_json::json!({
          "error": {
            "message": "This endpoint's maximum context length is 16384 tokens",
            "code": 400
          }
        }))
        .unwrap();
        let message =
            serde_json::from_str::<Response>(&content).context("Failed to parse response")?;
        let message = ChatCompletionMessage::try_from(message.clone());

        assert!(message.is_err());
        Ok(())
    }
}
