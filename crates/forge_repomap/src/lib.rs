pub mod error;
pub mod file;
pub mod graph;
pub mod helpers;
pub mod symbol;
pub mod tree_context;
pub mod tree_walker;
pub mod types;
mod analyser;

#[cfg(test)]
mod tests;

pub use error::RepoMapError;
pub use file::FileError;
pub use file::GitWalker;
pub use helpers::close_small_gaps_helper;
pub use symbol::{Symbol, SymbolIndex, SymbolKind};
pub use types::RepoMap;