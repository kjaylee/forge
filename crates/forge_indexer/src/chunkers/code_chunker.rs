use text_splitter::{ChunkConfig, CodeSplitter};
use tracing::info;

use crate::{chunkers::Chunker, loaders::FileLoad, token_counter::TokenCounter};
use std::path::PathBuf;

pub struct CodeChunker<'model> {
    model: &'model str,
    tokens_per_chunk: usize,
}

impl<'model> CodeChunker<'model> {
    pub fn new(model: &'model str, tokens_per_chunk: usize) -> Self {
        Self { model, tokens_per_chunk }
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Block {
    pub chunk: String,
    pub path: PathBuf,
}

impl Block {
    pub fn hash(&self) -> String {
        use blake3::Hasher as Blake3;
        let mut hasher = Blake3::new();
        hasher.update(self.path.display().to_string().as_bytes());
        hasher.update(self.chunk.as_bytes());
        let hash = hasher.finalize();
        hash.to_hex().to_string()
    }
}

/// Chunker trait for splitting documents into chunks
#[async_trait::async_trait]
impl<'model> Chunker for CodeChunker<'model> {
    type Input = Vec<FileLoad>;
    type Output = Vec<Block>;
    async fn chunk(&self, input: Self::Input) -> anyhow::Result<Self::Output> {
        info!("Chunking files {}", input.len());
        let blocks = input
            .into_iter()
            .map(|file| -> anyhow::Result<Vec<Block>> {
                // Step 2.1: create the chunk config
                let chunk_config = ChunkConfig::new(self.tokens_per_chunk)
                    .with_sizer(TokenCounter::new(self.model));
                let splitter = CodeSplitter::new(file.language, chunk_config)?;

                // Step 2.2: split the file into chunks
                let chunks = splitter
                    .chunks(&file.content)
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();

                // Step 2.3: create the blocks
                let blocks = chunks
                    .into_iter()
                    .map(|chunk| Block { chunk, path: file.path.clone() })
                    .collect::<Vec<_>>();

                Ok(blocks)
            })
            .collect::<anyhow::Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        info!("Chunked blocks {}", blocks.len());
        Ok(blocks)
    }
}
