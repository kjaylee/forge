use std::path::PathBuf;

use anyhow::Context;
use async_openai::types::{CreateEmbeddingRequest, EmbeddingInput};
use tracing::info;

use super::{Embedder, EmbedderInput, EmbedderOutput};
use crate::token_counter::TokenCounter;

#[derive(Clone)]
pub struct OpenAI {
    embedding_model: String,
    dims: u32,
    cache_path: PathBuf,
}

impl OpenAI {
    pub fn new<S: Into<String>>(embedding_model: S, dims: u32) -> Self {
        // Create a cache directory in the current working directory
        let cwd = std::env::current_dir().expect("Failed to get current directory");
        let embedding_model = embedding_model.into();
        let cache_path = cwd.join(format!(
            ".cache/openai-embeddings-{}-{}",
            embedding_model.replace('/', "_"),
            dims
        ));

        // Ensure the cache directory exists
        std::fs::create_dir_all(&cache_path).expect("Failed to create cache directory");

        Self { embedding_model, dims, cache_path }
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

#[derive(Debug, Clone)]
pub struct Embedding<Input> {
    pub input: Input,
    pub embedding: Vec<f32>,
}

fn hash<P: AsRef<str>>(payload: P) -> String {
    use blake3::Hasher as Blake3;
    let mut hasher = Blake3::new();
    hasher.update(payload.as_ref().as_bytes());
    let hash = hasher.finalize();
    hash.to_hex().to_string()
}

#[async_trait::async_trait]
impl Embedder for OpenAI {
    async fn embed<T, In>(
        &self,
        inputs: Vec<EmbedderInput<T>>,
    ) -> anyhow::Result<Vec<EmbedderOutput>>
    where
        T: ToString + Send,
        In: Into<EmbedderInput<T>> + Send,
    {
        info!("Embedding {} blocks", inputs.len());
        let mut result = Vec::with_capacity(inputs.len());
        for _ in 0..inputs.len() {
            result.push(None);
        }

        let inputs = inputs
            .into_iter()
            .map(|input: EmbedderInput<T>| input)
            .map(|m: EmbedderInput<T>| EmbedderInput { payload: m.payload.to_string() })
            .collect::<Vec<_>>();

        let mut uncached = Vec::new();

        // Check cache first
        let mut cache_hits = 0;
        for (i, block) in inputs.iter().enumerate() {
            let hash = hash(&block.payload);
            let key = format!("{}.{}:{}", self.embedding_model, self.dims, hash);

            // Try to get from disk cache
            match cacache::read(&self.cache_path, &key).await {
                Ok(cached_bytes) => {
                    // Convert bytes back to Vec<f32> using bytemuck
                    let cached: Vec<f32> = bytemuck::cast_slice(&cached_bytes).to_vec();
                    cache_hits += 1;

                    result[i] = Some(EmbedderOutput { embeddings: cached });
                    continue;
                }
                Err(_) => {
                    // Not in cache, will need to compute
                }
            }
            uncached.push((i, block));
        }

        info!("Uncached blocks: {}", uncached.len());

        // Process uncached items if any
        if !uncached.is_empty() {
            // Process batches of uncached texts
            let texts = uncached
                .iter()
                .map(|(_, p)| p.payload.to_string())
                .collect();
            let mut embeddings = Vec::new();

            for batch in EmbeddingBatcher::new(&self.embedding_model, 30_000).create_batches(texts)
            {
                let batch_results = self
                    .process_batch(batch, &self.embedding_model, self.dims)
                    .await?;
                embeddings.extend(batch_results);
            }

            // Update results and cache
            for (idx, (orig_idx, payload)) in uncached.iter().enumerate() {
                let embedding = embeddings[idx].clone();
                result[*orig_idx] = Some(EmbedderOutput { embeddings: embedding.clone() });
                let hash = hash(&payload.payload);
                let key = format!("{}.{}:{}", self.embedding_model, self.dims, hash);

                let bytes = bytemuck::cast_slice(&embedding).to_vec();
                cacache::write(&self.cache_path, &key, &bytes)
                    .await
                    .context("Failed to write to cache")?;
            }
        }

        info!("Cache hits: {}/{}", cache_hits, inputs.len());

        Ok(result.into_iter().flatten().collect())
    }
}

/// Helper struct to manage batching for embeddings generation with token limits
/// Follows the builder pattern for configuration
pub struct EmbeddingBatcher {
    /// Maximum tokens allowed per batch
    pub max_tokens_per_batch: usize,
    pub tokenizer: TokenCounter,
}

impl EmbeddingBatcher {
    pub fn new(model: &str, max_tokens_per_batch: usize) -> Self {
        Self { max_tokens_per_batch, tokenizer: TokenCounter::new(model) }
    }
}

impl EmbeddingBatcher {
    /// Estimate token count for a text
    pub fn estimate_tokens(&self, text: &str) -> usize {
        self.tokenizer.tokens(text)
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
