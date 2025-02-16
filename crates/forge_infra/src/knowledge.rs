use std::sync::Arc;

use anyhow::{anyhow, Context};
use forge_app::KnowledgeRepository;
use forge_domain::{self as domain, Environment, Knowledge, KnowledgeId, Query};
use qdrant_client::qdrant::{CreateCollectionBuilder, Distance, VectorParamsBuilder};
use qdrant_client::{Payload, Qdrant};
use serde_json::Value;
use tokio::sync::Mutex;

pub struct ForgeKnowledgeRepository {
    env: Environment,
    client: Arc<Mutex<Option<Arc<Qdrant>>>>,
    collection: String,
    size: u64,
}

impl ForgeKnowledgeRepository {
    pub fn new(env: Environment, collection: impl ToString, size: u64) -> Self {
        Self {
            env,
            client: Default::default(),
            collection: collection.to_string(),
            size,
        }
    }

    async fn client(&self) -> anyhow::Result<Arc<Qdrant>> {
        let mut guard = self.client.lock().await;
        if let Some(client) = guard.as_ref() {
            Ok(client.clone())
        } else {
            let client = Arc::new(
                Qdrant::from_url(
                    self.env
                        .qdrant_cluster
                        .as_ref()
                        .ok_or(anyhow!("Qdrant Cluster is not set"))?,
                )
                .api_key(
                    self.env
                        .qdrant_key
                        .as_ref()
                        .ok_or(anyhow!("Qdrant Key is not set"))?
                        .as_str(),
                )
                .build()
                .with_context(|| "Failed to connect to knowledge service")?,
            );

            client
                .create_collection(
                    CreateCollectionBuilder::new(self.collection.clone())
                        .vectors_config(VectorParamsBuilder::new(self.size, Distance::Cosine)),
                )
                .await
                .with_context(|| format!("Failed to create collection: {}", self.collection))?;

            *guard = Some(client.clone());

            Ok(client)
        }
    }
}

fn to_payload(json: Value) -> Payload {
    todo!()
}

#[async_trait::async_trait]
impl KnowledgeRepository<Value> for ForgeKnowledgeRepository {
    async fn store(&self, info: Vec<Knowledge<Value>>) -> anyhow::Result<()> {
        todo!()
    }

    async fn search(&self, query: Query) -> anyhow::Result<Vec<domain::Knowledge<Value>>> {
        todo!()
    }

    async fn list(&self) -> anyhow::Result<Vec<domain::Knowledge<Value>>> {
        todo!()
    }

    async fn drop(&self, ids: Vec<KnowledgeId>) -> anyhow::Result<()> {
        todo!()
    }
}
