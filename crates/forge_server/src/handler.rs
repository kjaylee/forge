use std::convert::Infallible;
use std::path::Path;
use std::sync::Arc;

use axum::extract::{Path as AxumPath, Query, State};
use axum::response::{IntoResponse, Response, Sse};
use axum::Json;
use forge_api::ForgeAPI;
use forge_domain::*;
use forge_services::Infrastructure;
use futures::stream::Stream;
use http::StatusCode;
use serde::Deserialize;
use serde_json::Value;

use crate::error::{Error, ErrorResponse, Result};
use crate::sse::message_stream_to_sse;

/// State shared between handlers
pub struct AppState<F> {
    pub api: Arc<ForgeAPI<F>>,
}

/// Handler for suggestions
pub async fn suggestions<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
) -> Result<Json<Vec<File>>> {
    let suggestions = state.api.suggestions().await?;
    Ok(Json(suggestions))
}

/// Handler for tools
pub async fn tools<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
) -> Json<Vec<ToolDefinition>> {
    let tools = state.api.tools().await;
    Json(tools)
}

/// Handler for models
pub async fn models<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
) -> Result<Json<Vec<Model>>> {
    let models = state.api.models().await?;
    Ok(Json(models))
}

/// Handler for chat
pub async fn chat<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    Json(chat_request): Json<ChatRequest>,
) -> std::result::Result<
    Sse<impl Stream<Item = std::result::Result<axum::response::sse::Event, Infallible>>>,
    Error,
> {
    let stream = state.api.chat(chat_request).await?;
    Ok(Sse::new(message_stream_to_sse(stream)))
}

/// Handler for environment
pub async fn environment<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
) -> Json<Environment> {
    let env = state.api.environment();
    Json(env)
}

/// Handler for initializing a conversation
pub async fn init<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    workflow: Option<Json<Workflow>>,
) -> Result<Json<ConversationId>> {
    let conversation_id = match workflow {
        Some(Json(workflow)) => state.api.init(workflow).await?,
        None => state.api.init(Workflow::default()).await?,
    };
    Ok(Json(conversation_id))
}

/// Parameters for load handler
#[derive(Deserialize)]
pub struct LoadParams {
    path: Option<String>,
}

/// Handler for loading a workflow
pub async fn load<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    Query(params): Query<LoadParams>,
) -> Result<Json<Workflow>> {
    let path_ref = params.path.as_ref().map(Path::new);
    let workflow = state.api.load(path_ref).await?;
    Ok(Json(workflow))
}

/// Handler for getting a conversation
pub async fn conversation<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    AxumPath(conversation_id): AxumPath<ConversationId>,
) -> Result<Json<Conversation>> {
    let conversation = state
        .api
        .conversation(&conversation_id)
        .await?
        .ok_or_else(|| Error::ConversationNotFound(conversation_id.to_string()))?;

    Ok(Json(conversation))
}

/// Parameters for variable operations
#[derive(Deserialize)]
pub struct VariableParams {
    pub key: String,
}

/// Handler for getting a variable
pub async fn get_variable<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    AxumPath(conversation_id): AxumPath<ConversationId>,
    Query(params): Query<VariableParams>,
) -> Result<Json<Option<Value>>> {
    let value = state
        .api
        .get_variable(&conversation_id, &params.key)
        .await?;
    Ok(Json(value))
}

/// Handler for setting a variable
pub async fn set_variable<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    AxumPath(conversation_id): AxumPath<ConversationId>,
    Query(params): Query<VariableParams>,
    Json(value): Json<Value>,
) -> Result<StatusCode> {
    state
        .api
        .set_variable(&conversation_id, params.key, value)
        .await?;

    Ok(StatusCode::OK)
}

/// Handler for upserting a conversation
pub async fn upsert_conversation<F: Services + Infrastructure>(
    State(state): State<Arc<AppState<F>>>,
    Json(conversation): Json<Conversation>,
) -> Result<StatusCode> {
    state.api.upsert_conversation(conversation).await?;
    Ok(StatusCode::OK)
}

// Convert errors to HTTP responses
impl IntoResponse for Error {
    fn into_response(self) -> Response {
        let (status, error_message) = match self {
            Error::ConversationNotFound(_) => (StatusCode::NOT_FOUND, self.to_string()),
            Error::InvalidParameter(_) => (StatusCode::BAD_REQUEST, self.to_string()),
            _ => (StatusCode::INTERNAL_SERVER_ERROR, self.to_string()),
        };

        let body = Json(ErrorResponse { error: error_message });

        (status, body).into_response()
    }
}
