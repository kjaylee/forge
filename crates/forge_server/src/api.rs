use std::sync::Arc;

const SERVER_PORT: u16 = 8080;

use axum::extract::{Json, Path, State};
use axum::http::StatusCode;
use axum::response::sse::{Event, Sse};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::Router;
use forge_provider::{AnyMessage, Model};
use forge_tool::Tool;
use serde::Serialize;
use tokio_stream::{Stream, StreamExt};
use tower_http::cors::{Any, CorsLayer};
use tracing::info;

use crate::app::{App, ChatRequest};
use crate::completion::File;
use crate::server::Server;
use crate::Result;

pub struct API {
    // TODO: rename Conversation to Server and drop Server
    state: Arc<Server>,
}

impl Default for API {
    fn default() -> Self {
        dotenv::dotenv().ok();
        let api_key = std::env::var("FORGE_KEY").expect("FORGE_KEY must be set");
        Self { state: Arc::new(Server::new(".", api_key)) }
    }
}

impl API {
    pub async fn launch(self) -> Result<()> {
        tracing_subscriber::fmt().init();

        if dotenv::dotenv().is_ok() {
            info!("Loaded .env file");
        }

        // Setup HTTP server
        let app = Router::new()
            .route("/conversations", get(list_conversations_handler))
            .route("/conversation", post(conversation_handler))
            .route("/conversations/:id", get(conversation_history_handler))
            .route("/completions", get(completions_handler))
            .route("/health", get(health_handler))
            .route("/tools", get(tools_handler))
            .route("/models", get(models_handler))
            .route("/context", get(context_handler))
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
            .with_state(self.state.clone());

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

#[axum::debug_handler]
async fn conversation_handler(
    State(state): State<Arc<Server>>,
    Json(request): Json<ChatRequest>,
) -> Sse<impl Stream<Item = std::result::Result<Event, std::convert::Infallible>>> {
    let stream = state
        .chat(request)
        .await
        .expect("Engine failed to respond with a chat message");
    Sse::new(stream.map(|action| {
        let data = serde_json::to_string(&action).expect("Failed to serialize action");
        Ok(Event::default().data(data))
    }))
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

async fn context_handler(State(state): State<Arc<Server>>) -> Json<AppResponse> {
    let app = state.context().await;
    Json(AppResponse { app })
}

async fn conversation_history_handler(
    State(state): State<Arc<Server>>,
    Path(id): Path<String>,
) -> Response {
    let app = state.context().await;
    match app.conversation_history.get(&id) {
        Some(messages) => Json(ConversationResponse { messages: messages.clone() }).into_response(),
        None => (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse { error: format!("Conversation with id '{}' not found", id) }),
        )
            .into_response(),
    }
}

async fn list_conversations_handler(
    State(state): State<Arc<Server>>,
) -> Json<ConversationsResponse> {
    let app = state.context().await;
    let conversations = app
        .conversation_history
        .iter()
        .map(|(id, messages)| ConversationInfo { id: id.clone(), messages: messages.clone() })
        .collect();

    Json(ConversationsResponse { conversations })
}

#[derive(Serialize)]
pub struct AppResponse {
    app: App,
}

#[derive(Serialize)]
pub struct ModelResponse {
    models: Vec<Model>,
}

#[derive(Serialize)]
pub struct ToolResponse {
    tools: Vec<Tool>,
}

#[derive(Serialize)]
pub struct ConversationResponse {
    messages: Vec<AnyMessage>,
}

#[derive(Serialize)]
pub struct ConversationInfo {
    id: String,
    messages: Vec<AnyMessage>,
}

#[derive(Serialize)]
pub struct ConversationsResponse {
    conversations: Vec<ConversationInfo>,
}

#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    error: String,
}
