use super::*;
use insta::assert_snapshot;
use tempfile::TempDir;
use tokio::fs;

pub mod typescript;
pub mod tsx;
pub mod css;
pub mod java;
pub mod scala;