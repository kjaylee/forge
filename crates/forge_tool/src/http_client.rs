use reqwest::{Client, Request};
use anyhow;
use bytes::Bytes;

#[async_trait::async_trait]
pub trait HttpIO: Send + Sync + 'static {
    async fn execute(&self, request: Request) -> anyhow::Result<Bytes>;
}

pub struct ReqwestClient {
    client: Client,
}

impl Default for ReqwestClient { 
    fn default() -> Self {
        Self {
            client: Client::new(),
        }
    }
}

#[async_trait::async_trait]
impl HttpIO for ReqwestClient {
    async fn execute(&self, request: Request) -> anyhow::Result<Bytes> {
        let response = self.client.execute(request).await?;
        response.bytes().await.map_err(Into::into)
    }
}

#[cfg(test)]
pub mod test_utils {
    use super::*;
    use std::sync::Mutex;

    pub struct MockHttpIO {
        responses: Mutex<Vec<Bytes>>,
    }

    impl MockHttpIO {
        pub fn new(responses: Vec<Vec<u8>>) -> Self {
            Self {
                responses: Mutex::new(responses.into_iter().map(Bytes::from).collect()),
            }
        }
    }

    #[async_trait::async_trait]
    impl HttpIO for MockHttpIO {
        async fn execute(&self, _request: Request) -> anyhow::Result<Bytes> {
            self.responses
                .lock()
                .unwrap()
                .pop()
                .ok_or_else(|| anyhow::anyhow!("No more responses"))
        }
    }
}
