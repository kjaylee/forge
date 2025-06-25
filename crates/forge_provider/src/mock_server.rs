use mockito::{Mock, Server, ServerGuard};

pub struct MockServer {
    server: ServerGuard,
}

impl MockServer {
    pub async fn new() -> Self {
        let server = Server::new_async().await;
        Self { server }
    }
    pub async fn mock_models(&mut self, body: serde_json::Value, status: usize) -> Mock {
        self.server
            .mock("GET", "/models")
            .with_status(status)
            .with_header("content-type", "application/json")
            .with_body(body.to_string())
            .create_async()
            .await
    }

    pub fn url(&self) -> String {
        self.server.url()
    }
}
