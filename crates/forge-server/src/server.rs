use std::convert::Infallible;
use std::sync::Arc;

use axum::extract::State;
use axum::response::sse::{Event, Sse};
use axum::routing::{get, post};
use axum::Router;
use forge_tool::permission::{Permission, PermissionRequest};
use forge_tool::ToolTrait;
use futures::stream::Stream;
use serde_json::json;
use tokio::sync::RwLock;
use tower_http::cors::{Any, CorsLayer};
use tracing::info;

use crate::app::App;
use crate::completion::{Completion, File};
use crate::Result;

pub struct Server {
    state: Arc<App>,
}

impl Default for Server {
    fn default() -> Self {
        Self { state: Arc::new(App::new(".")) }
    }
}

impl Server {
    pub async fn launch(self) -> Result<()> {
        tracing_subscriber::fmt().init();

        if dotenv::dotenv().is_ok() {
            info!("Loaded .env file");
        }

        // Setup HTTP server
        let app = Router::new()
            // .route("/conversation", get(conversation_handler))
            .route("/test", get(test_handler))
            .route("/completions", get(completions_handler))
            .route("/event-response", post(event_response_handler))
            .route("/health", get(health_handler))
            .route("/events", get(events_handler))
            .layer(CorsLayer::new().allow_origin(Any))
            .with_state(self.state.clone());

        // Spawn HTTP server
        let server = tokio::spawn(async move {
            let listener = tokio::net::TcpListener::bind("127.0.0.1:3000")
                .await
                .unwrap();
            info!("Server running on http://127.0.0.1:3000");
            axum::serve(listener, app).await.unwrap();
        });

        // Wait for server to complete (though it runs indefinitely)
        let _ = server.await;

        Ok(())
    }
}

async fn test_handler(State(st): State<Arc<App>>) -> axum::Json<serde_json::Value> {
    let permission_tool = Permission::new(Arc::new(RwLock::new(st.transport.clone())));
    let result = permission_tool
        .call(PermissionRequest {
            action: "delete_file".to_string(),
            context: None,
            request_id: "1".to_string(),
        })
        .await
        .unwrap();
    axum::Json(json!({"status": result.granted}))
}

async fn event_response_handler(
    State(state): State<Arc<App>>,
    mut body: axum::Json<serde_json::Value>,
) -> axum::Json<serde_json::Value> {
    // as soon as we get the response, we send the response back to it's tool.
    println!("[Finder]: at Server.rs body: {:#?} ", body);
    println!(
        "[Finder]: sender: {:#?} ",
        state.transport.event_response_sender.is_empty()
    );

    let _result = state.transport.event_response_sender.send(body.take());
    axum::Json(json!({}))
}

async fn completions_handler() -> axum::Json<Vec<File>> {
    let completions = Completion::new(".").list().await;
    axum::Json(completions)
}

async fn events_handler(
    State(state): State<Arc<App>>,
) -> Sse<impl Stream<Item = std::result::Result<Event, Infallible>>> {
    use futures::StreamExt;
    use tokio_stream::wrappers::BroadcastStream;
    // TODO: move transport_ctx from app_state to request_ctx.
    let recv = state.transport.event_sender.subscribe();
    let stream = BroadcastStream::new(recv).map(|value| {
        let value = value.unwrap();
        let json = serde_json::to_string(&value).unwrap_or_default();
        Ok(Event::default().data(json))
    });

    Sse::new(stream).keep_alive(
        axum::response::sse::KeepAlive::new()
            .interval(std::time::Duration::from_secs(1))
            .text("keep-alive-text"),
    )
}

// async fn conversation_handler(
//     State(state): State<Arc<App>>,
// ) -> Sse<impl Stream<Item = std::result::Result<Event, Infallible>>> {
//     Sse::new(state.as_stream().await)
// }

async fn health_handler() -> axum::response::Response {
    axum::response::Response::builder()
        .status(200)
        .body(axum::body::Body::empty())
        .unwrap()
}
