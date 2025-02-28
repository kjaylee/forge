//! # Forge Display
//!
//! The `forge_display` crate provides comprehensive display and formatting functionality 
//! for the Code Forge application, handling all user-facing output styling and visualization.
//!
//! ## Features
//!
//! * Diff formatting for displaying file changes in the terminal
//! * Grep output styling for search results
//! * Title formatting for consistent UI headings
//! * VS Code integration for visualizing diffs in the editor
//! * Streaming diff updates with animation capabilities
//! 
//! ## Modules
//! 
//! * `diff` - Formats file differences with syntax highlighting
//! * `grep` - Styles search results with context
//! * `title` - Creates formatted section titles
//! * `vscode_diff` - Integrates with VS Code for live diff viewing
//!
//! ## Usage
//!
//! This crate is primarily used by other Code Forge components to ensure
//! consistent, user-friendly output formatting across the application.
pub mod diff;
pub mod grep;
pub mod title;
pub mod vscode_diff;

// Re-export commonly used types and functions
pub use diff::DiffFormat;
pub use grep::GrepFormat;
pub use title::*;
pub use vscode_diff::{VsCodeDiffConfig, create_streaming_diff_viewer};
