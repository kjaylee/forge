use hnsw_rs::prelude::*;
use serde_json::Value;
use std::{collections::HashMap, sync::RwLock};
use tracing::info;

use super::{QueryOptions, QueryOutput, Store, StoreInput};

pub struct HnswStore<'a> {
    hnsw: RwLock<Hnsw<'a, f32, DistCosine>>,
    payloads: RwLock<HashMap<usize, Value>>,
    id: RwLock<usize>,
    dimension: usize,
}

impl<'a> HnswStore<'a> {
    pub fn new(dimension: usize) -> Self {
        // HNSW parameters
        let max_nb_connection = 16;
        let nb_layer = 16.min((dimension as f32).ln().floor() as usize);
        let ef_construction = 200;

        // Create HNSW index
        let hnsw = Hnsw::new(
            max_nb_connection,
            dimension,
            nb_layer,
            ef_construction,
            DistCosine,
        );

        Self {
            hnsw: RwLock::new(hnsw),
            payloads: RwLock::new(HashMap::new()),
            id: RwLock::new(0),
            dimension,
        }
    }

    fn get_next_id(&self) -> usize {
        let mut id = self.id.write().unwrap();
        let new_id = *id;
        *id += 1;
        new_id
    }
}

#[async_trait::async_trait]
impl Store for HnswStore<'_> {
    async fn store<T>(&self, inputs: Vec<StoreInput<T>>) -> anyhow::Result<()>
    where
        T: Into<serde_json::Value> + Send + Sync,
    {
        info!("Storing embeddings in In-memory");
        let hnsw = self.hnsw.write().unwrap();
        let mut payloads = self.payloads.write().unwrap();

        let inputs_with_identifier = inputs
            .into_iter()
            .map(|input| {
                let id = self.get_next_id();
                (
                    id,
                    StoreInput {
                        embeddings: input.embeddings,
                        metadata: input.metadata.into(),
                    },
                )
            })
            .collect::<Vec<(usize, StoreInput<serde_json::Value>)>>();

        // First collect all payloads
        for (id, input) in &inputs_with_identifier {
            if input.embeddings.len() != self.dimension {
                return Err(anyhow::anyhow!(
                    "Vector dimension mismatch: expected {}, got {}",
                    self.dimension,
                    input.embeddings.len()
                ));
            }
            payloads.insert(*id, input.metadata.clone());
        }

        // Prepare data for parallel insertion
        let data: Vec<_> = inputs_with_identifier
            .into_iter()
            .map(|(id, input)| (input.embeddings, id))
            .collect();

        // Convert to vector of references for parallel_insert
        let data_refs: Vec<_> = data.iter().map(|(vec, id)| (vec, *id)).collect();

        // Insert all vectors in parallel
        hnsw.parallel_insert(&data_refs);

        info!("Stored embeddings in In-memory");

        Ok(())
    }
    async fn query<T>(
        &self,
        query: Vec<f32>,
        options: QueryOptions,
    ) -> anyhow::Result<Vec<QueryOutput<T>>>
    where
        T: serde::de::DeserializeOwned + Send + Sync,
    {
        if query.len() != self.dimension {
            return Err(anyhow::anyhow!(
                "Vector dimension mismatch: expected {}, got {}",
                self.dimension,
                query.len()
            ));
        }

        info!("Querying in-memory embeddings");

        let hnsw = self.hnsw.read().unwrap();
        let payloads = self.payloads.read().unwrap();
        let limit = options.limit;

        // Search for nearest neighbors
        // Using a fixed ef_search value of 100 (should be >= limit)
        let ef_search = std::cmp::max(100, limit * 2);
        let nearest = hnsw.search(&query, limit as usize, ef_search as usize);

        // Convert to SearchResult format
        let results = nearest
            .iter()
            .filter_map(|neighbor| {
                payloads.get(&neighbor.d_id).cloned().and_then(|payload| {
                    match serde_json::from_value::<T>(payload) {
                        Ok(deserialized_payload) => Some(QueryOutput {
                            score: 1.0 - neighbor.distance,
                            payload: deserialized_payload,
                        }),
                        Err(_) => None,
                    }
                })
            })
            .collect::<Vec<_>>();

        info!("Retrieved {} results from Qdrant", results.len());

        Ok(results)
    }
}

// Implement Default for convenience
impl Default for HnswStore<'static> {
    fn default() -> Self {
        Self::new(384) // Default dimension, adjust as needed
    }
}
