use thiserror::Error;

/// Errors that can occur during repository analysis.
#[derive(Debug, Error)]
pub enum Error {
    /// An error occurred during file I/O operations
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// Failed to parse source code or queries
    #[error("Parse error: {0}")]
    Parse(String),

    /// Attempted to analyze a file in an unsupported language
    #[error("Unsupported language: {0}")]
    UnsupportedLanguage(String),

    /// An error occurred in the tree-sitter parser
    #[error("Tree-sitter error: {0}")]
    TreeSitter(String),

    /// A provided path was invalid
    #[error("Invalid path: {0}")]
    InvalidPath(String),
}
