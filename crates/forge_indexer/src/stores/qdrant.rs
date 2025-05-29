use std::sync::Arc;

use async_trait::async_trait;
use futures::future::join_all;
use qdrant_client::{
    Payload,
    qdrant::{PointStruct, UpsertPointsBuilder},
};
use tracing::info;
use uuid::Uuid;

use super::{Store, StoreInput};

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
    async fn store<T>(&self, inputs: Vec<StoreInput<T>>) -> anyhow::Result<()>
    where
        T: Into<serde_json::Value> + Send + Sync,
    {
        info!("Storing embeddings in Qdrant");
        let mut points = Vec::with_capacity(inputs.len());
        for input in inputs {
            let vector = input.embeddings;
            let id = Uuid::new_v4().to_string();
            let payload: Payload = input.metadata.into().try_into()?;
            let point = PointStruct::new(id, vector, payload);
            points.push(point);
        }

        // Process batches in parallel
        let futures = points.chunks(40).map(|batch| {
            let client = Arc::clone(&self.client);
            let collection_name = self.collection_name.clone();
            async move {
                client
                    .upsert_points(UpsertPointsBuilder::new(collection_name, batch))
                    .await
            }
        });

        // Join all futures and collect results
        let _results = join_all(futures).await;

        info!("Stored embeddings in Qdrant");

        Ok(())
    }
}
