use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub enum GrepError {
    IoError(std::io::Error),
    PatternError(String),
}

impl fmt::Display for GrepError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GrepError::IoError(err) => write!(f, "IO error: {}", err),
            GrepError::PatternError(msg) => write!(f, "Pattern error: {}", msg),
        }
    }
}

impl Error for GrepError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            GrepError::IoError(err) => Some(err),
            GrepError::PatternError(_) => None,
        }
    }
}

impl From<std::io::Error> for GrepError {
    fn from(err: std::io::Error) -> Self {
        GrepError::IoError(err)
    }
}

pub type Result<T> = std::result::Result<T, GrepError>;
