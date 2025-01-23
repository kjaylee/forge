#[derive(Debug, thiserror::Error)]
pub enum LanguageError {
    #[error("Parser initialization failed: {0}")]
    ParserInitError(String),
    
    #[error("Failed to parse source: {0}")]
    ParseError(String),
    
    #[error("Invalid query pattern: {0}")]
    QueryError(String),
    
    #[error("Language not supported: {0}")]
    UnsupportedLanguage(String),
}

pub type Result<T> = std::result::Result<T, LanguageError>;