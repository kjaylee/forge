use forge_treesitter::Parser;
use tracing::info;

use super::Chunker;
use crate::{FileLoad, TokenCounter};

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
    async fn chunk(&self, input: Vec<FileLoad>) -> anyhow::Result<Vec<forge_treesitter::Block>> {
        let tokenizer = TokenCounter::try_from(self.model)?;
        // TODO: can be done in parallel.
        let blocks = input
            .into_iter()
            .filter_map(|file| {
                file.path
                    .extension()
                    .map(|ext| ext.to_string_lossy().to_string())
                    .and_then(|ext| {
                        Parser::try_from(ext.as_str())
                            .map_err(|e| eprintln!("failed to create parser: {e}"))
                            .ok()
                            .and_then(|mut parser| {
                                parser
                                    .parse(&file.path, &file.content)
                                    .map_err(|e| eprintln!("failed to parse file contents: {e}"))
                                    .ok()
                            })
                    })
            })
            .flatten()
            .collect::<Vec<_>>();

        let total_blocks = blocks.len();
        info!("Total code blocks: {}", total_blocks);

        let filter_blocks = blocks
            .into_iter()
            .filter(|block| tokenizer.count_tokens(&block.snippet) <= self.max_tokens)
            .collect::<Vec<_>>();

        let filtered_blocks_count = filter_blocks.len();

        info!(
            "After filtering {} blocks eliminated, total blocks: {} ",
            total_blocks - filtered_blocks_count,
            filtered_blocks_count
        );

        Ok(filter_blocks)
    }
}
