use std::sync::Arc;
use std::pin::Pin;

const SERVER_PORT: u16 = 8080;

use axum::extract::{Json, State};
use axum::response::sse::{Event, Sse};
use axum::response::Html;
use axum::routing::{get, post};
use axum::Router;
use forge_env::Environment;
use forge_provider::{Model, Request};
use forge_tool::ToolDefinition;
use serde::Serialize;
use tokio_stream::{Stream, StreamExt};
use tower_http::cors::{Any, CorsLayer};
use tracing::info;

use crate::app::{ChatRequest, ChatResponse};
use crate::completion::File;
use crate::context::ContextEngine;
use crate::server::Server;
use crate::Result;

pub struct API {
    // TODO: rename Conversation to Server and drop Server
    api_key: String,
}

impl Default for API {
    fn default() -> Self {
        dotenv::dotenv().ok();
        let api_key = std::env::var("FORGE_KEY").expect("FORGE_KEY must be set");
        Self { api_key }
    }
}

async fn context_html_handler(State(state): State<Arc<Server>>) -> Html<String> {
    let context = state.context().await;
    let engine = ContextEngine::new(context);
    Html(engine.render_html())
}

impl API {
    pub async fn launch(self) -> Result<()> {
        tracing_subscriber::fmt().init();
        let env = Environment::from_env().await?;
        let state = Arc::new(Server::new(env, self.api_key));

        if dotenv::dotenv().is_ok() {
            info!("Loaded .env file");
        }

        // Setup HTTP server
        let app = Router::new()
            .route("/conversation", post(conversation_handler))
            .route("/completions", get(completions_handler))
            .route("/health", get(health_handler))
            .route("/tools", get(tools_handler))
            .route("/models", get(models_handler))
            .route("/context", get(context_handler))
            .route("/context/html", get(context_html_handler))
            .layer(
                CorsLayer::new()
                    .allow_origin(Any)
                    .allow_methods([
                        axum::http::Method::GET,
                        axum::http::Method::POST,
                        axum::http::Method::OPTIONS,
                    ])
                    .allow_headers([
                        axum::http::header::CONTENT_TYPE,
                        axum::http::header::AUTHORIZATION,
                    ]),
            )
            .with_state(state.clone());

        // Spawn HTTP server
        let server = tokio::spawn(async move {
            let listener = tokio::net::TcpListener::bind(format!("127.0.0.1:{SERVER_PORT}"))
                .await
                .unwrap();
            info!("Server running on http://127.0.0.1:{SERVER_PORT}");
            axum::serve(listener, app).await.unwrap();
        });

        // Wait for server to complete (though it runs indefinitely)
        let _ = server.await;

        Ok(())
    }
}

use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};

// Error response type for HTTP endpoints
#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    message: String,
}

impl IntoResponse for crate::Error {
    fn into_response(self) -> Response {
        let status = match self {
            crate::Error::Provider(_) => StatusCode::BAD_GATEWAY,
            crate::Error::EmptyResponse => StatusCode::NO_CONTENT,
            _ => StatusCode::INTERNAL_SERVER_ERROR,
        };

        let body = ErrorResponse {
            error: self.to_string(),
            message: format!("{:?}", self),
        };

        (status, axum::Json(body)).into_response()
    }
}

// Type alias for API results using our custom error type
type ApiResult<T> = std::result::Result<T, crate::Error>;

// Type alias for SSE event stream
type SseEvent = std::result::Result<Event, std::convert::Infallible>;
type EventStream = Pin<Box<dyn Stream<Item = SseEvent> + Send>>;

async fn completions_handler(
    State(state): State<Arc<Server>>,
) -> ApiResult<axum::Json<Vec<File>>> {
    let files = state.completions().await?;
    Ok(axum::Json(files))
}

#[axum::debug_handler]
async fn conversation_handler(
    State(state): State<Arc<Server>>,
    Json(request): Json<ChatRequest>,
) -> std::result::Result<Sse<EventStream>, std::convert::Infallible> {
    Ok(match state.chat(request).await {
        Ok(response_stream) => {
            let mapped_stream = response_stream.map(|response| {
                let event_data = match &response {
                    ChatResponse::Fail(error) => {
                        // Try to parse error as JSON first
                        match serde_json::from_str::<serde_json::Value>(error) {
                            Ok(json) => json.to_string(),
                            Err(_) => serde_json::json!({
                                "error": {
                                    "type": "chat_error",
                                    "message": error
                                }
                            }).to_string()
                        }
                    },
                    _ => match serde_json::to_string(&response) {
                        Ok(data) => data,
                        Err(e) => serde_json::json!({
                            "error": {
                                "type": "serialization_error",
                                "message": e.to_string()
                            }
                        }).to_string(),
                    }
                };
                Ok(Event::default().data(event_data))
            });
            Sse::new(Box::pin(mapped_stream) as EventStream)
        }
        Err(e) => {
            let error_data = match e {
                crate::Error::Provider(provider_err) => {
                    match provider_err {
                        forge_provider::Error::Provider { provider, error } => serde_json::json!({
                            "error": {
                                "type": "provider_error",
                                "provider": provider,
                                "message": error.to_string(),
                                "details": match error {
                                    forge_provider::ProviderError::UpstreamError(value) => value,
                                    _ => serde_json::Value::String(error.to_string())
                                }
                            }
                        }),
                        _ => serde_json::json!({
                            "error": {
                                "type": "provider_error",
                                "message": provider_err.to_string()
                            }
                        })
                    }
                },
                _ => serde_json::json!({
                    "error": {
                        "type": "chat_error",
                        "message": e.to_string()
                    }
                })
            }.to_string();
            Sse::new(Box::pin(tokio_stream::once(Ok(Event::default().data(error_data)))) as EventStream)
        }
    })
}

#[axum::debug_handler]
async fn tools_handler(State(state): State<Arc<Server>>) -> ApiResult<Json<ToolResponse>> {
    let tools = state.tools();
    Ok(Json(ToolResponse { tools }))
}

async fn health_handler() -> Response {
    StatusCode::OK.into_response()
}

async fn models_handler(
    State(state): State<Arc<Server>>,
) -> ApiResult<Json<ModelResponse>> {
    let models = state.models().await?;
    Ok(Json(ModelResponse { models }))
}

async fn context_handler(State(state): State<Arc<Server>>) -> Json<ContextResponse> {
    let context = state.context().await;
    Json(ContextResponse { context })
}

#[derive(Serialize)]
pub struct ContextResponse {
    context: Request,
}

#[derive(Serialize)]
pub struct ModelResponse {
    models: Vec<Model>,
}

#[derive(Serialize)]
pub struct ToolResponse {
    tools: Vec<ToolDefinition>,
}
