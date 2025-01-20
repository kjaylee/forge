/// Estimates the number of tokens in a text string using programming-aware
/// tokenization rules.
pub fn estimate_tokens(text: &str) -> usize {
    let mut token_count = 0;

    // Common programming token patterns
    const PATTERNS: &[&str] = &[
        // Symbols that are usually separate tokens
        "->", "=>", "::", "//", "/*", "*/", "#{", "${", // Operators
        "+", "-", "*", "/", "=", "!", "|", "&", "<", ">", // Brackets and punctuation
        "(", ")", "[", "]", "{", "}", ",", ";", ".", ":",
    ];

    // Split into words and process each
    for word in text.split_whitespace() {
        // Add base word as one token
        token_count += 1;

        // Check for common programming patterns
        for &pattern in PATTERNS {
            if word.contains(pattern) {
                // Each pattern is counted as a separate token
                token_count += word.matches(pattern).count();

                // Count non-empty parts around the pattern
                let parts: Vec<_> = word.split(pattern).filter(|s| !s.is_empty()).collect();
                token_count += parts.len();
            }
        }
    }

    // Count line breaks as they often represent structural tokens
    token_count += text.matches('\n').count();

    // Add overhead for potential subtokenization
    token_count += token_count / 5;

    token_count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_estimation() {
        // Test simple text
        let simple = "Hello world";
        let count = estimate_tokens(simple);
        assert_eq!(
            count, 2,
            "Expected 2 tokens for '{}', got {}",
            simple, count
        );

        // Test code-like text
        let code = "fn test() -> Result<(), Error> {\n    println!(\"test\");\n}";
        let count = estimate_tokens(code);
        assert!(
            count >= 20,
            "Expected at least 20 tokens for code block, got {}\nCode:\n{}",
            count,
            code
        );

        // Test operator splitting
        let ops = "a + b * c";
        let count = estimate_tokens(ops);
        assert!(
            count >= 5,
            "Expected at least 5 tokens for '{}', got {}",
            ops,
            count
        );

        // Test common patterns
        let patterns = "impl Trait for Type {}";
        let count = estimate_tokens(patterns);
        assert!(
            count >= 5,
            "Expected at least 5 tokens for '{}', got {}",
            patterns,
            count
        );

        // Test with paths and type parameters
        let complex = "std::collections::HashMap<String, Vec<T>>";
        let count = estimate_tokens(complex);
        assert!(
            count >= 10,
            "Expected at least 10 tokens for '{}', got {}",
            complex,
            count
        );
    }
}
