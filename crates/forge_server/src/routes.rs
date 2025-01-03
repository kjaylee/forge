use std::sync::Arc;

const SERVER_PORT: u16 = 8080;

use axum::extract::{Json, State};
use axum::response::sse::{Event, Sse};
use axum::response::{Html, Json as AxumJson};
use axum::routing::{get, post};
use axum::Router;
use forge_env::Environment;
use forge_provider::{
    CompletionMessage, ContentMessage, Model, Request, Role, ToolCall, ToolCallId, ToolCallPart,
    ToolResult,
};
use forge_tool::ToolDefinition;
use serde::Serialize;
use tokio_stream::{Stream, StreamExt};
use tower_http::cors::{Any, CorsLayer};
use tracing::info;
use utoipa::OpenApi;

use crate::context::ContextEngine;
use crate::{
    ChatRequest, ChatResponse, Errata, File, Result, RootAPIService, Service, ToolUseStart,
};

#[derive(OpenApi)]
#[openapi(
    paths(
        health_handler,
        conversation_handler,
        completions_handler,
        tools_handler,
        models_handler,
        context_handler,
        context_html_handler,
        openapi_handler
    ),
    components(
        schemas(
            ChatRequest,
            ChatResponse,
            ToolResponse,
            ModelResponse,
            ContextResponse,
            File,
            Errata,
            ToolUseStart,
            CompletionMessage,
            ContentMessage,
            Role,
            ToolCall,
            ToolCallPart,
            ToolCallId,
            ToolResult,
            Model,
            ToolDefinition,
            Request
        )
    ),
    tags(
        (name = "forge", description = "Forge API endpoints")
    ),
    external_docs(
        url = "https://github.com/tailcallhq/code-forge",
        description = "Code Forge Repository"
    )
)]
struct ApiDoc;

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

/// Get context as HTML
#[utoipa::path(
    get,
    path = "/context/html",
    tag = "forge",
    responses(
        (status = 200, description = "Context rendered as HTML", body = String)
    )
)]
async fn context_html_handler(State(state): State<Arc<dyn RootAPIService>>) -> Html<String> {
    let context = state.context().await;
    let engine = ContextEngine::new(context);
    Html(engine.render_html())
}

impl API {
    pub async fn launch(self) -> Result<()> {
        tracing_subscriber::fmt().init();
        let env = Environment::from_env().await?;
        let state = Arc::new(Service::root_api_service(env, self.api_key));

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
            .route("/openapi.json", get(openapi_handler))
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

/// Get file completions
#[utoipa::path(
    get,
    path = "/completions",
    tag = "forge",
    responses(
        (status = 200, description = "List of files", body = Vec<File>)
    )
)]
async fn completions_handler(
    State(state): State<Arc<dyn RootAPIService>>,
) -> axum::Json<Vec<File>> {
    let files = state
        .completions()
        .await
        .expect("Failed to get completions");
    axum::Json(files)
}

#[axum::debug_handler]
/// Start a conversation
#[utoipa::path(
    post,
    path = "/conversation",
    tag = "forge",
    request_body = ChatRequest,
    responses(
        (status = 200, description = "Server-sent events stream of chat responses", content_type = "text/event-stream", body = ChatResponse)
    )
)]
async fn conversation_handler(
    State(state): State<Arc<dyn RootAPIService>>,
    Json(request): Json<ChatRequest>,
) -> Sse<impl Stream<Item = std::result::Result<Event, std::convert::Infallible>>> {
    let stream = state
        .chat(request)
        .await
        .expect("Engine failed to respond with a chat message");
    Sse::new(stream.map(|message| {
        let data = serde_json::to_string(
            &message.unwrap_or_else(|error| ChatResponse::Error(Errata::from(&error))),
        )
        .expect("Failed to serialize message");
        Ok(Event::default().data(data))
    }))
}

#[axum::debug_handler]
/// Get available tools
#[utoipa::path(
    get,
    path = "/tools",
    tag = "forge",
    responses(
        (status = 200, description = "List of available tools", body = ToolResponse)
    )
)]
async fn tools_handler(State(state): State<Arc<dyn RootAPIService>>) -> Json<ToolResponse> {
    let tools = state.tools().await;
    Json(ToolResponse { tools })
}

/// Health check endpoint
#[utoipa::path(
    get,
    path = "/health",
    tag = "forge",
    responses(
        (status = 200, description = "Server is healthy")
    )
)]
async fn health_handler() -> axum::response::Response {
    axum::response::Response::builder()
        .status(200)
        .body(axum::body::Body::empty())
        .unwrap()
}

/// Get available models
#[utoipa::path(
    get,
    path = "/models",
    tag = "forge",
    responses(
        (status = 200, description = "List of available models", body = ModelResponse)
    )
)]
async fn models_handler(State(state): State<Arc<dyn RootAPIService>>) -> Json<ModelResponse> {
    let models = state.models().await.unwrap_or_default();
    Json(ModelResponse { models })
}

/// Get current context
#[utoipa::path(
    get,
    path = "/context",
    tag = "forge",
    responses(
        (status = 200, description = "Current context", body = ContextResponse)
    )
)]
async fn context_handler(State(state): State<Arc<dyn RootAPIService>>) -> Json<ContextResponse> {
    let context = state.context().await;
    Json(ContextResponse { context })
}

#[derive(Serialize, utoipa::ToSchema)]
pub struct ContextResponse {
    #[schema(example = json!({"messages": [], "model": "gpt-4"}))]
    pub context: Request,
}

#[derive(Serialize, utoipa::ToSchema)]
pub struct ModelResponse {
    #[schema(value_type = Vec<Model>, example = json!([{"id": "gpt-4", "name": "GPT-4"}]))]
    pub models: Vec<Model>,
}

#[derive(Serialize, utoipa::ToSchema)]
pub struct ToolResponse {
    #[schema(value_type = Vec<ToolDefinition>, example = json!([{"name": "read_file", "description": "Read file contents"}]))]
    pub tools: Vec<ToolDefinition>,
}

/// Get OpenAPI documentation
#[utoipa::path(
    get,
    path = "/openapi.json",
    tag = "forge",
    responses(
        (status = 200, description = "OpenAPI specification", body = String)
    )
)]
async fn openapi_handler() -> AxumJson<serde_json::Value> {
    AxumJson(serde_json::json!(ApiDoc::openapi()))
}
