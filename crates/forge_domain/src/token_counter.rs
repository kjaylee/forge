use tiktoken_rs::CoreBPE;

/// Maximum number of tokens allowed in tool output

const BPE_MODEL: &str = "gpt-4-0314";

/// TokenCounter struct for counting tokens in text using tiktoken
#[derive(Clone)]
pub struct TokenCounter {
    bpe: CoreBPE,
}

impl Default for TokenCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl TokenCounter {
    // TODO: make this configurable
    pub const MAX_TOOL_OUTPUT_TOKENS: usize = 10_000;

    /// Create a new TokenCounter using the GPT-4 tokenizer
    pub fn new() -> Self {
        let bpe = tiktoken_rs::get_bpe_from_model(BPE_MODEL).unwrap();
        Self { bpe }
    }

    /// Count the number of tokens in the given text
    pub fn count_tokens(&self, text: &str) -> usize {
        self.bpe.encode_with_special_tokens(text).len()
    }
}
