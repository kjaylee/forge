use axum::{
    extract::Query,
    response::Html,
    routing::get,
    Router,
};
use std::collections::HashMap;
use tokio::net::TcpListener;
use thiserror::Error;

/// Errors that can occur during callback handling
#[derive(Error, Debug)]
pub enum CallbackError {
    #[error("Callback timed out after {0} seconds")]
    Timeout(u64),
    
    #[error("Server error: {0}")]
    ServerError(String),
}

/// The result of a successful callback
#[derive(Debug, Clone)]
pub struct CallbackResult {
    pub state: String,
    pub code: String,
}

/// A server that handles OAuth callbacks
pub struct CallbackServer {
    port: u16,
}

impl Default for CallbackServer {
    fn default() -> Self {
        Self { port: 8080 }
    }
}


impl CallbackServer {
    /// Create a new callback server
    pub fn new(port: u16) -> Self {
        Self { port }
    }
    
    /// Start the server and wait for a callback
    pub async fn wait_for_callback(&self, timeout_secs: u64) -> Result<CallbackResult, CallbackError> {
        let (tx, rx) = tokio::sync::oneshot::channel();
        let tx = std::sync::Arc::new(std::sync::Mutex::new(Some(tx)));
        
        let app = Router::new().route("/callback", get(move |Query(params): Query<HashMap<String, String>>| {
            let tx = tx.clone();
            async move {
                if let Some(err) = params.get("error") {
                    return Html(format!(
                        "<html><body><h1>Authentication Error</h1><p>Error: {}</p></body></html>",
                        err
                    ));
                }

                match (params.get("state"), params.get("code")) {
                    (Some(state), Some(code)) => {
                        let result = CallbackResult {
                            state: state.to_string(),
                            code: code.to_string(),
                        };
                        
                        if let Some(tx) = tx.lock().unwrap().take() {
                            let _ = tx.send(result);
                        }
                        Html("<html><body><h1>Authentication Successful</h1><p>You can now close this window and return to the application.</p></body></html>".to_string())
                    }
                    _ => Html("<html><body><h1>Authentication Error</h1><p>Missing required parameters</p></body></html>".to_string())
                }
            }
        }));

        let listener = TcpListener::bind(format!("127.0.0.1:{}", self.port))
            .await
            .map_err(|e| CallbackError::ServerError(e.to_string()))?;

        // Start server in background
        let server = axum::serve(listener, app.into_make_service());
        tokio::spawn(async move {
            server.await.unwrap();
        });

        // Wait for callback with timeout
        match tokio::time::timeout(
            std::time::Duration::from_secs(timeout_secs),
            rx
        ).await {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(_)) => Err(CallbackError::ServerError("Failed to receive callback".to_string())),
            Err(_) => Err(CallbackError::Timeout(timeout_secs))
        }
    }
}
