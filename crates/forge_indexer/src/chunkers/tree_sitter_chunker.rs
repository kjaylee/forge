use forge_treesitter::Block;
use tracing::info;

use crate::{FileLoad, TokenCounter};

use super::Chunker;

pub struct TreeSitterChunker<'model> {
    model: &'model str,
    max_tokens: usize,
}

impl<'model> TreeSitterChunker<'model> {
    pub fn new(model: &'model str, max_tokens: usize) -> Self {
        Self { model, max_tokens }
    }
}

#[async_trait::async_trait]
impl<'model> Chunker for TreeSitterChunker<'model> {
    type Input = Vec<FileLoad>;
    type Output = Vec<Block>;
    async fn chunk(&self, input: Self::Input) -> anyhow::Result<Self::Output> {
        let mut parser = forge_treesitter::RustTreeSitter::default();
        let token_counter = TokenCounter::new(self.model);
        // extract code blocks from source code and keep blocks only if tokens are less than max_tokens
        let blocks = input
            .into_iter()
            .filter_map(|file| match parser.parse(&file.path, &file.content) {
                Ok(blocks) => Some(blocks),
                Err(e) => {
                    eprintln!("failed to parse the file contents: {}", e);
                    None
                }
            })
            .flatten()
            .collect::<Vec<_>>();

        let total_blocks = blocks.len();

        let filtered_blocks = blocks
            .into_iter()
            .filter(|block| token_counter.tokens(&block.snippet) < self.max_tokens)
            .collect::<Vec<_>>();

        let filtered_blocks_count = filtered_blocks.len();

        info!(
            "Total blocks: {}, Filtered blocks: {}",
            total_blocks, filtered_blocks_count
        );

        Ok(filtered_blocks)
    }
}
