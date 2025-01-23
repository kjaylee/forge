mod language;
mod error;
mod parser;
mod query;
mod registry;
mod languages;

pub use language::LanguageSyntaxConfig;
pub use error::{LanguageError, Result};
pub use parser::{Parser, ParsedSource};
pub use query::{QueryEngine, QueryMatch, QueryCapture};
pub use registry::LanguageRegistry;

// Re-export language configurations
pub use languages::*;