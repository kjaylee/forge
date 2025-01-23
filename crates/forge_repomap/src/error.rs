use thiserror::Error;
use forge_language::LanguageError;

use crate::FileError;

#[derive(Debug, Error)]
pub enum RepoMapError {
    #[error("I/O error")]
    IoError,

    #[error("Parse error: {0}")]
    ParseError(String),

    #[error("Symbol analysis error: {0}")]
    SymbolAnalysisError(String),

    #[error("Graph analysis error: {0}")]
    GraphAnalysisError(String),

    #[error("Tree generation error: {0}")]
    TreeGenerationError(String),

    #[error("From FS helper error: {0}")]
    FileSystemError(#[from] FileError),

    #[error("Language error: {0}")]
    LanguageError(#[from] LanguageError),
}