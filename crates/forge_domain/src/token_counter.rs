use tiktoken_rs::CoreBPE;

/// Maximum number of tokens allowed in tool output
pub const MAX_TOOL_OUTPUT_TOKENS: usize = 10_000;

/// TokenCounter struct for counting tokens in text using tiktoken
#[derive(Clone)]
pub struct TokenCounter {
    bpe: CoreBPE,
    pub max_tokens: usize,
}

impl TokenCounter {
    /// Create a new TokenCounter using the GPT-4 tokenizer
    pub fn new() -> Self {
        let bpe = tiktoken_rs::get_bpe_from_model("gpt-4-0314").unwrap();
        Self { bpe , max_tokens: MAX_TOOL_OUTPUT_TOKENS }
    }

    /// Count the number of tokens in the given text
    pub fn count_tokens(&self, text: &str) -> usize {
        self.bpe.encode_with_special_tokens(text).len()
    }
}