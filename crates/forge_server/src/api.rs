use std::sync::{Arc, RwLock};

const SERVER_PORT: u16 = 8080;

use axum::extract::{Json, Path, State};
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

use crate::app::ChatRequest;
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
        let state = Arc::new(Server::new(env, self.api_key).await);

        if dotenv::dotenv().is_ok() {
            info!("Loaded .env file");
        }

        // Setup HTTP server
        let app = Router::new()
            .route("/conversation/:id", get(conversation_by_id_handler))
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

async fn completions_handler(State(state): State<Arc<Server>>) -> axum::Json<Vec<File>> {
    let files = state
        .completions()
        .await
        .expect("Failed to get completions");
    axum::Json(files)
}

// execute the chat_request against the chat ctx.
#[axum::debug_handler]
async fn conversation_handler(
    State(state): State<Arc<Server>>,
    Json(mut request): Json<ChatRequest>,
) -> Sse<impl Stream<Item = std::result::Result<Event, std::convert::Infallible>>> {
    let conversation_id = request
        .conversation_id
        .clone()
        .unwrap_or_else(|| uuid::Uuid::new_v4().to_string());
    request.conversation_id = Some(conversation_id.clone());

    println!("[Finder]: conversation_id: {}", conversation_id);

    // 1. pull the conversation context from database.
    let conversation_ctx = state
        .storage()
        .get(conversation_id)
        .await
        .expect("Failed to get conversation context.")
        .unwrap_or_else(|| state.base_context());

    let conversation_ctx = Arc::new(RwLock::new(conversation_ctx));

    let stream = state
        .chat(request, conversation_ctx)
        .await
        .expect("Engine failed to respond with a chat message");

    Sse::new(stream.map(|action| {
        let data = serde_json::to_string(&action).expect("Failed to serialize action");
        Ok(Event::default().data(data))
    }))
}

async fn conversation_by_id_handler(
    State(state): State<Arc<Server>>,
    Path(id): Path<String>,
) -> std::result::Result<Json<Request>, (axum::http::StatusCode, String)> {
    match state.storage().get(id).await {
        Ok(Some(history)) => Ok(Json(history)),
        Ok(None) => Err((
            axum::http::StatusCode::NOT_FOUND,
            "Conversation not found".to_string(),
        )),
        Err(e) => Err((
            axum::http::StatusCode::INTERNAL_SERVER_ERROR,
            format!("Failed to retrieve conversation: {}", e),
        )),
    }
}

#[axum::debug_handler]
async fn tools_handler(State(state): State<Arc<Server>>) -> Json<ToolResponse> {
    let tools = state.tools();
    Json(ToolResponse { tools })
}

async fn health_handler() -> axum::response::Response {
    axum::response::Response::builder()
        .status(200)
        .body(axum::body::Body::empty())
        .unwrap()
}

async fn models_handler(State(state): State<Arc<Server>>) -> Json<ModelResponse> {
    let models = state.models().await.unwrap_or_default();
    Json(ModelResponse { models })
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
