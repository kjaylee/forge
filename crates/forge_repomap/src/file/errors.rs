use thiserror::Error;
use std::io;

#[derive(Debug, Error)]
pub enum FileError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    
    #[error("Git error: {0}")]
    Git(String),
    
    #[error("Path error: {0}")]
    Path(String),
}

pub type Result<T> = std::result::Result<T, FileError>;