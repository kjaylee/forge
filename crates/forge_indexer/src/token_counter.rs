use text_splitter::ChunkSizer;

/// Token counter for counting tokens in a chunk
pub struct TokenCounter<'model>(&'model str);

impl<'model> TokenCounter<'model> {
    pub fn new(model: &'model str) -> Self {
        Self(model)
    }

    /// Return the tokens present in the text
    pub fn tokens(&self, text: &str) -> usize {
        let tokenizer = tiktoken_rs::get_bpe_from_model(self.0).unwrap();
        tokenizer.encode_ordinary(text).len()
    }
}

impl<'model> ChunkSizer for TokenCounter<'model> {
    fn size(&self, chunk: &str) -> usize {
        self.tokens(chunk)
    }
}
