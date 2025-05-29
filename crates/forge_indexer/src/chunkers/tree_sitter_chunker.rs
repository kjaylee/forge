use forge_treesitter::Block;

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
            .filter(|block| token_counter.tokens(&block.snippet) < self.max_tokens)
            .collect::<Vec<_>>();

        Ok(blocks)
    }
}
