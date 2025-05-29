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
    cache: Cache,
}

impl OpenAI {
    pub fn new<S: Into<String>>(embedding_model: S, dims: u32) -> Self {
        let embedding_model = embedding_model.into();
        let cwd = std::env::current_dir().expect("failed to retrive current working directory.");
        let cache_path = cwd.join(format!(
            ".cache/openai-embeddings-{}-{}",
            embedding_model.replace('/', "_"),
            dims
        ));

        Self {
            embedding_model,
            dims,
            cache: Cache::try_from(cache_path).expect("failed to create cache path"),
        }
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
        info!("Embedding {} blocks", inputs.len());
        let mut result = vec![None; inputs.len()];

        let inputs = inputs
            .into_iter()
            .map(|input: EmbedderInput<T>| EmbedderInput { payload: input.payload.to_string() })
            .collect::<Vec<_>>();

        let mut uncached = Vec::new();

        // Check cache first
        let mut cache_hits = 0;

        // TODO: can be parallelized
        for (i, block) in inputs.iter().enumerate() {
            let cache_key = format!("{}.{}:{}", self.embedding_model, self.dims, block.hash());
            match self.cache.get(&cache_key).await {
                Some(embeddings) => {
                    cache_hits += 1;
                    result[i] = Some(EmbedderOutput { embeddings });
                }
                None => {
                    uncached.push((i, block));
                }
            }
        }

        info!("Uncached blocks: {}", uncached.len());

        // Process uncached items if any
        if !uncached.is_empty() {
            // Process batches of uncached texts
            let texts = uncached
                .iter()
                .map(|(_, p)| p.payload.to_string())
                .collect::<Vec<_>>();
            // Pre-allocate with the exact capacity we need
            let mut embeddings = Vec::with_capacity(texts.len());

            // 30,000 is limit of OpenAi embedding API.
            // TODO: can be parallelized
            let batches =
                EmbeddingBatcher::try_new(&self.embedding_model, 30_000)?.create_batches(texts);
            for batch in batches {
                let batch_results = self
                    .process_batch(batch, &self.embedding_model, self.dims)
                    .await?;
                embeddings.extend(batch_results);
            }

            // TODO: can be parallelized
            // Update results and cache
            for (idx, embeddings) in embeddings.into_iter().enumerate() {
                let (pos, block) = &uncached[idx];
                let cache_key = format!("{}.{}:{}", self.embedding_model, self.dims, block.hash());
                let _ = self.cache.put(&cache_key, &embeddings).await;
                result[*pos] = Some(EmbedderOutput { embeddings });
            }
        }

        info!("Cache hits: {}/{}", cache_hits, inputs.len());

        Ok(result.into_iter().flatten().collect())
    }
}

#[derive(Clone)]
struct Cache(PathBuf);

impl TryFrom<PathBuf> for Cache {
    type Error = anyhow::Error;
    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        std::fs::create_dir_all(&path).context("failed to create cache directory")?;
        Ok(Self(path))
    }
}

impl Cache {
    async fn get(&self, cache_key: &str) -> Option<Vec<f32>> {
        cacache::read(&self.0, cache_key)
            .await
            .map(|cached_bytes| bytemuck::cast_slice(&cached_bytes).to_vec())
            .ok()
    }

    async fn put(&self, cache_key: &str, cache_value: &[f32]) -> anyhow::Result<()> {
        let bytes: Vec<u8> = bytemuck::cast_slice(cache_value).to_vec();
        cacache::write(&self.0, cache_key, &bytes).await?;
        Ok(())
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
