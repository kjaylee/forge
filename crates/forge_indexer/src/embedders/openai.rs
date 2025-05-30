use std::path::Path;

use async_openai::types::{CreateEmbeddingRequest, EmbeddingInput};
use tracing::info;

use super::{CachedEmbedder, Embedder, EmbedderInput, EmbedderOutput};
use crate::token_counter::TokenCounter;

/// Maximum tokens supported by OpenAI embedding batch endpoint.
const TOKEN_LIMIT_PER_BATCH: usize = 30_000;

#[derive(Clone)]
pub struct OpenAI {
    model: String,
    dims: u32,
}

impl OpenAI {
    pub fn new<S: Into<String>>(embedding_model: S, dims: u32) -> Self {
        Self { model: embedding_model.into(), dims }
    }

    /// Creates a cached version of the OpenAI embedder
    pub fn cached(
        cache_path: &Path,
        embedding_model: impl Into<String>,
        dims: u32,
    ) -> anyhow::Result<CachedEmbedder<OpenAI>> {
        let model_name = embedding_model.into();
        CachedEmbedder::try_new(cache_path, OpenAI::new(&model_name, dims), model_name, dims)
    }

    /// Process a single batch of texts to get embeddings
    async fn process_batch(
        &self,
        batch: Vec<String>,
        model: &str,
        dims: u32,
    ) -> anyhow::Result<Vec<Vec<f32>>> {
        let result = async_openai::Client::new()
            .embeddings()
            .create(CreateEmbeddingRequest {
                model: model.into(),
                input: EmbeddingInput::StringArray(batch),
                encoding_format: Some(async_openai::types::EncodingFormat::Float),
                dimensions: Some(dims),
                user: None,
            })
            .await?;

        Ok(result.data.into_iter().map(|d| d.embedding).collect())
    }
}

#[async_trait::async_trait]
impl Embedder for OpenAI {
    async fn embed<T>(&self, inputs: Vec<EmbedderInput<T>>) -> anyhow::Result<Vec<EmbedderOutput>>
    where
        T: ToString + Send,
    {
        info!("Embedding {} blocks with OpenAI", inputs.len());

        // Process batches of texts
        let texts = inputs
            .iter()
            .map(|p| p.payload.to_string())
            .collect::<Vec<_>>();

        // Pre-allocate with the exact capacity we need
        let mut embeddings = Vec::with_capacity(texts.len());

        // 30,000 is limit of OpenAI embedding API.
        let batches =
            EmbeddingBatcher::try_new(&self.model, TOKEN_LIMIT_PER_BATCH)?.create_batches(texts);
        for batch in batches {
            let batch_results = self.process_batch(batch, &self.model, self.dims).await?;
            embeddings.extend(batch_results);
        }

        // Convert to EmbedderOutput format
        let results = embeddings
            .into_iter()
            .map(|embeddings| EmbedderOutput { embeddings })
            .collect();

        Ok(results)
    }
}

/// Helper struct to manage batching for embeddings generation with token limits
pub struct EmbeddingBatcher {
    /// Maximum tokens allowed per batch
    pub max_tokens_per_batch: usize,
    pub tokenizer: TokenCounter,
}

impl EmbeddingBatcher {
    pub fn try_new(model: &str, max_tokens_per_batch: usize) -> anyhow::Result<Self> {
        Ok(Self {
            max_tokens_per_batch,
            tokenizer: TokenCounter::try_from(model)?,
        })
    }
}

impl EmbeddingBatcher {
    /// Estimate token count for a text
    pub fn estimate_tokens(&self, text: &str) -> usize {
        self.tokenizer.count_tokens(text)
    }

    /// Create batches from input texts respecting token limits
    pub fn create_batches(&self, texts: Vec<String>) -> Vec<Vec<String>> {
        let mut batches = Vec::new();
        let mut current_batch = Vec::new();
        let mut current_batch_tokens = 0;

        for text in texts {
            let token_estimate = self.estimate_tokens(&text);

            // If a single text exceeds the limit, we could either:
            // 1. Skip it (bad for completeness)
            // 2. Truncate it (bad for meaning)
            // 3. Process it alone (may fail but gives API a chance to handle it)
            // We choose option 3 here
            if token_estimate > self.max_tokens_per_batch {
                if !current_batch.is_empty() {
                    batches.push(std::mem::take(&mut current_batch));
                    current_batch_tokens = 0;
                }
                batches.push(vec![text]);
                continue;
            }

            // If adding this would exceed the batch limit, finalize current batch
            if current_batch_tokens + token_estimate > self.max_tokens_per_batch
                && !current_batch.is_empty()
            {
                batches.push(std::mem::take(&mut current_batch));
                current_batch_tokens = 0;
            }

            // Add to current batch
            current_batch_tokens += token_estimate;
            current_batch.push(text);
        }

        // Don't forget the last batch if it has items
        if !current_batch.is_empty() {
            batches.push(current_batch);
        }

        batches
    }
}
