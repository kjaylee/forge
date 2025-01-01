use std::sync::Arc;

const SERVER_PORT: u16 = 8080;

use axum::extract::{Json, Path, State};
use axum::response::sse::{Event, Sse};
use axum::routing::{get, post};
use axum::Router;
use forge_env::Environment;
use forge_provider::{Model, Request};
use forge_tool::ToolDefinition;
use serde::Serialize;
use tokio::sync::Mutex;
use tokio_stream::{Stream, StreamExt};
use tower_http::cors::{Any, CorsLayer};
use tracing::info;

use crate::app::{Action, App, ChatRequest, State as AppState};
use crate::completion::File;
use crate::runtime::ExecutionContext;
use crate::server::Server;
use crate::storage::SqliteStorage;
use crate::{Result, Storage};

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

impl API {
    pub async fn launch(self) -> Result<()> {
        tracing_subscriber::fmt().init();
        let env = Environment::from_env().await?;
        let storage = Arc::new(SqliteStorage::default().await?);
        let state = Arc::new(Server::new(env, storage, self.api_key));

        if dotenv::dotenv().is_ok() {
            info!("Loaded .env file");
        }

        // Setup HTTP server
        let app = Router::new()
            .route("/conversations", get(all_conversations_handler))
            .route("/conversation/:id", get(conversation_by_id_handler))
            .route("/conversation", post(conversation_handler))
            .route("/completions", get(completions_handler))
            .route("/health", get(health_handler))
            .route("/tools", get(tools_handler))
            .route("/models", get(models_handler))
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

async fn completions_handler<S: Storage + 'static>(
    State(state): State<Arc<Server<S>>>,
) -> axum::Json<Vec<File>> {
    let files = state
        .completions()
        .await
        .expect("Failed to get completions");
    axum::Json(files)
}

// execute the chat_request against the chat ctx.
async fn conversation_handler<S: Storage + 'static>(
    State(state): State<Arc<Server<S>>>,
    Json(mut request): Json<ChatRequest>,
) -> Sse<impl Stream<Item = std::result::Result<Event, std::convert::Infallible>>> {
    let conversation_id = request
        .conversation_id
        .clone()
        .unwrap_or_else(|| uuid::Uuid::new_v4().to_string());
    request.conversation_id = Some(conversation_id.clone());

    dbg!(&conversation_id);

    let message = format!("<task>{}</task>", request.content);
    let request = request.content(message);

    // // 1. pull the conversation context from database.
    let mut exec_ctx = state
        .storage()
        .get(&conversation_id)
        .await
        .expect("Failed to get conversation context.")
        .unwrap_or_else(|| ExecutionContext {
            state: state.app().with_conversation_id(conversation_id.clone()),
            action: Action::UserMessage(request.clone()),
        });
    // since we are not trying to restore, in order to execute the present request
    // we replace the action with the new request.
    exec_ctx.action = Action::UserMessage(request);

    let exec_ctx = Arc::new(Mutex::new(exec_ctx));

    let stream = state
        .chat(exec_ctx)
        .await
        .expect("Engine failed to respond with a chat message");

    Sse::new(stream.map(|action| {
        let data = serde_json::to_string(&action).expect("Failed to serialize action");
        Ok(Event::default().data(data))
    }))
}

// TODO: expose better errors to the client. eg why the conversation failed.
async fn conversation_by_id_handler<S: Storage + 'static>(
    State(state): State<Arc<Server<S>>>,
    Path(id): Path<String>,
) -> std::result::Result<Json<ExecutionContext<AppState, Action>>, (axum::http::StatusCode, String)>
{
    match state.storage().get(&id).await {
        Ok(Some(history)) => Ok(Json(history)),
        Ok(None) => Err((
            axum::http::StatusCode::NOT_FOUND,
            "Conversation not found".to_string(),
        )),
        Err(_e) => Err((
            axum::http::StatusCode::INTERNAL_SERVER_ERROR,
            "Failed to retrieve conversation".to_string(),
        )),
    }
}

async fn tools_handler<S: Storage + 'static>(
    State(state): State<Arc<Server<S>>>,
) -> Json<ToolResponse> {
    let tools = state.tools();
    Json(ToolResponse { tools })
}

async fn health_handler() -> axum::response::Response {
    axum::response::Response::builder()
        .status(200)
        .body(axum::body::Body::empty())
        .unwrap()
}

async fn models_handler<S: Storage + 'static>(
    State(state): State<Arc<Server<S>>>,
) -> Json<ModelResponse> {
    let models = state.models().await.unwrap_or_default();
    Json(ModelResponse { models })
}

// TODO: currently we return all the conversations, we should paginate this.
async fn all_conversations_handler<S: Storage + 'static>(
    State(state): State<Arc<Server<S>>>,
) -> Json<Vec<ExecutionContext<App, Action>>> {
    let chat_history = state.storage().list().await.unwrap_or_default();
    Json(chat_history)
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
