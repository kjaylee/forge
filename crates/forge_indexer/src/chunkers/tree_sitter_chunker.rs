use forge_treesitter::Block;

use crate::FileLoad;

use super::Chunker;

#[derive(Default)]
pub struct TreeSitterChunker;

#[async_trait::async_trait]
impl Chunker for TreeSitterChunker {
    type Input = Vec<FileLoad>;
    type Output = Vec<Block>;
    async fn chunk(&self, input: Self::Input) -> anyhow::Result<Self::Output> {
        let mut parser = forge_treesitter::RustTreeSitter::default();

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

        Ok(blocks)
    }
}
