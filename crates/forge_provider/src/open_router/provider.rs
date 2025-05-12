use std::time::Duration;

use anyhow::{Context as _, Result};
use derive_builder::Builder;
use forge_domain::{
    self, ChatCompletionMessage, Context as ChatContext, Model, ModelId, Provider, ProviderService,
    ResultStream, RetryConfig,
};
use reqwest::header::{HeaderMap, HeaderValue, AUTHORIZATION};
use reqwest::{Client, Url};
use reqwest_eventsource::{Event, RequestBuilderExt};
use tokio_stream::StreamExt;
use tracing::debug;

use super::model::{ListModelResponse, OpenRouterModel};
use super::request::OpenRouterRequest;
use super::response::OpenRouterResponse;
use crate::open_router::transformers::{ProviderPipeline, Transformer};
use crate::retry::StatusCodeRetryPolicy;
use crate::retry_utils::RetryHandler;
use crate::utils::format_http_context;

#[derive(Clone, Builder)]
pub struct OpenRouter {
    client: Client,
    provider: Provider,
    #[builder(default = "RetryConfig::default()")]
    retry_config: RetryConfig,
}

impl OpenRouter {
    pub fn builder() -> OpenRouterBuilder {
        OpenRouterBuilder::default()
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
        let mut request = OpenRouterRequest::from(context)
            .model(model.clone())
            .stream(true);
        request = ProviderPipeline::new(&self.provider).transform(request);

        let url = self.url("chat/completions")?;

        debug!(
            url = %url,
            model = %model,
            message_count = %request.message_count(),
            message_cache_count = %request.message_cache_count(),
            "Connecting Upstream"
        );

        let mut es = self
            .client
            .post(url.clone())
            .headers(self.headers())
            .json(&request)
            .eventsource()
            .context(format_http_context(None, "POST", &url))?;
        let status_codes = self.retry_config.retry_status_codes.clone();

        es.set_retry_policy(Box::new(StatusCodeRetryPolicy::new(
            Duration::from_millis(self.retry_config.initial_backoff_ms),
            self.retry_config.backoff_factor as f64,
            None, // No maximum duration
            Some(self.retry_config.max_retry_attempts),
            status_codes.clone(),
        )));

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
                            serde_json::from_str::<OpenRouterResponse>(&message.data)
                                .with_context(|| format!("Failed to parse OpenRouter response: {}", message.data))
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
                            Some(Err(anyhow::anyhow!(error).context(format!("Http Status: {status_code}"))))
                        }
                        error => {
                            if crate::utils::is_tls_handshake_eof(&error) {
                                debug!(error = %error, "TLS handshake EOF detected - treating as end of stream");
                                None
                            } else {
                                debug!(error = %error, "Failed to receive chat completion event");
                                Some(Err(error.into()))
                            }
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

    async fn inner_models(&self) -> Result<Vec<Model>> {
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
                    Err(err) => {
                        // For other errors, propagate with context
                        let ctx_msg = format_http_context(err.status(), "GET", &url);
                        Err(anyhow::anyhow!(err)
                            .context(ctx_msg)
                            .context("Failed to fetch the models"))
                    }
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
impl ProviderService for OpenRouter {
    async fn chat(
        &self,
        model: &ModelId,
        context: ChatContext,
    ) -> ResultStream<ChatCompletionMessage, anyhow::Error> {
        self.inner_chat(model, context).await
    }

    async fn models(&self) -> Result<Vec<Model>> {
        RetryHandler::new(self.retry_config.clone())
            .retry(|| async { self.inner_models().await })
            .await
    }
}

impl From<OpenRouterModel> for Model {
    fn from(value: OpenRouterModel) -> Self {
        Model {
            id: value.id,
            name: value.name,
            description: value.description,
            context_length: value.context_length,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;
    use std::net::TcpListener;
    use std::sync::{Arc, Mutex};

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
        let message = serde_json::from_str::<OpenRouterResponse>(&content)
            .context("Failed to parse response")?;
        let message = ChatCompletionMessage::try_from(message.clone());

        assert!(message.is_err());
        Ok(())
    }

    #[tokio::test]
    async fn test_open_router_models_tls_handshake_eof() {
        // Create and start a simple TCP server that will simulate TLS handshake EOF
        let listener = TcpListener::bind("127.0.0.1:9443").unwrap();
        listener.set_nonblocking(true).unwrap();

        let running = Arc::new(Mutex::new(true));
        let running_clone = Arc::clone(&running);

        let retry_attempt = Arc::new(Mutex::new(0));
        let retry_attemp_clone = Arc::clone(&retry_attempt);

        // Spawn a thread to handle connections
        std::thread::spawn(move || {
            while *running_clone.lock().unwrap() {
                match listener.accept() {
                    Ok((mut stream, _)) => {
                        let mut retry_attemp_clone = retry_attemp_clone.lock().unwrap();
                        *retry_attemp_clone += 1;
                        // Read the initial TLS handshake data but don't respond
                        let _ = stream.set_nonblocking(false);
                        let mut buffer = [0u8; 1024];
                        let _ = stream.read(&mut buffer);
                        // Drop the connection without completing the handshake
                        drop(stream);
                    }
                    Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        std::thread::sleep(Duration::from_millis(10));
                    }
                    Err(_) => break,
                }
            }
        });

        // Create a reqwest client
        let client = reqwest::Client::builder()
            .timeout(Duration::from_secs(5))
            .build()
            .context("Failed to build client")
            .unwrap();

        // Create an OpenRouter instance that points to our mock server
        let mut provider = Provider::open_router("dummy");
        provider.open_ai_url("https://127.0.0.1:9443".into());

        let retry_config = RetryConfig::default().max_retry_attempts(2usize);
        let open_router = OpenRouter { client, provider, retry_config };
        let result = open_router.models().await;

        assert!(result.is_err());
        assert_eq!(*retry_attempt.lock().unwrap(), 3);

        // Clean up
        let mut running_guard = running.lock().unwrap();
        *running_guard = false;
    }
}
