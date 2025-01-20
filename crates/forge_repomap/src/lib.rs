//! A library for analyzing and understanding code repositories.
//!
//! The forge_repomap crate provides tools for building a comprehensive map of a
//! code repository, including:
//! - Symbol extraction (functions, classes, etc.)
//! - Dependency tracking between files
//! - Importance scoring for code elements
//! - Context generation for LLMs
//!
//! # Core Types
//! - [`RepoMap`]: The main entry point for repository analysis
//! - [`Symbol`]: Represents a defined symbol in the code
//! - [`Location`]: Specifies where a symbol is defined or referenced
//!
//! # Example
//! ```no_run
//! use std::path::PathBuf;
//! use forge_repomap::RepoMap;
//!
//! // Create a new repo map with a token budget
//! let mut repo_map = RepoMap::new(PathBuf::from("./"), 1000).unwrap();
//!
//! // Analyze the repository
//! repo_map.analyze().unwrap();
//!
//! // Get context about specific files
//! let context = repo_map.get_context(&[PathBuf::from("src/main.rs")]);
//! ```

mod error;
mod graph;
mod parser;
pub mod ranking; // Make the ranking module public
mod repo_map;
mod symbol;

pub use error::Error;
pub use ranking::{PageRank, PageRankConfig, SymbolReference};
pub use repo_map::RepoMap;
pub use symbol::{Location, Symbol, SymbolKind};
