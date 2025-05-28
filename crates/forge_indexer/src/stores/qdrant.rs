use std::sync::Arc;

use crate::Embedding;
use async_trait::async_trait;
use qdrant_client::{
    Payload,
    qdrant::{PointStruct, UpsertPointsBuilder},
};
use tracing::info;
use uuid::Uuid;

use super::Store;

#[derive(Clone)]
pub struct QdrantStore {
    client: Arc<qdrant_client::Qdrant>,
    collection_name: String,
}

impl QdrantStore {
    pub fn try_new<S: Into<String>, U: AsRef<str>>(
        url: U,
        api_key: S,
        collection_name: S,
    ) -> anyhow::Result<Self> {
        let client = Arc::new(
            qdrant_client::Qdrant::from_url(url.as_ref())
                .api_key(api_key.into())
                .skip_compatibility_check()
                .build()?,
        );

        Ok(Self { collection_name: collection_name.into(), client })
    }
}

#[async_trait]
impl Store for QdrantStore {
    type Input = Vec<Embedding>;
    async fn store(&self, inputs: Self::Input) -> anyhow::Result<()> {
        info!("Storing embeddings in Qdrant");
        let mut points = Vec::with_capacity(inputs.len());
        for input in inputs {
            let vector = input.embedding;
            let metadata = input.input;

            let id = Uuid::new_v4().to_string();
            let payload: Payload = serde_json::json!({
                "path": metadata.path,
            })
            .try_into()?;
            let point = PointStruct::new(id, vector, payload);
            points.push(point);
        }

        for batch in points.chunks(40) {
            let _ = self
                .client
                .upsert_points(UpsertPointsBuilder::new(
                    self.collection_name.clone(),
                    batch,
                ))
                .await?;
        }

        info!("Stored embeddings in Qdrant");

        Ok(())
    }
}
