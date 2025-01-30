use tiktoken_rs::CoreBPE;

const BPE_MODEL: &str = "gpt-4-0314";

/// TokenCounter struct for counting tokens in text using tiktoken
#[derive(Clone)]
pub struct TokenCounter {
    bpe: CoreBPE,
}

impl Default for TokenCounter {
    fn default() -> Self {
        let bpe = tiktoken_rs::get_bpe_from_model(BPE_MODEL).unwrap();
        Self { bpe }
    }
}

impl TokenCounter {
    /// Count the number of tokens in the given text
    pub fn count_tokens(&self, text: &str) -> usize {
        self.bpe.encode_with_special_tokens(text).len()
    }
}
