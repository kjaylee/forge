use text_splitter::ChunkSizer;
use tiktoken_rs::CoreBPE;

/// Token counter for counting tokens in a chunk
pub struct TokenCounter(CoreBPE);

impl TokenCounter {
    pub fn new(model: &str) -> Self {
        Self(tiktoken_rs::get_bpe_from_model(model).unwrap())
    }

    /// Return the tokens present in the text
    pub fn tokens(&self, text: &str) -> usize {
        self.0.encode_ordinary(text).len()
    }
}

impl ChunkSizer for TokenCounter {
    fn size(&self, chunk: &str) -> usize {
        self.tokens(chunk)
    }
}
