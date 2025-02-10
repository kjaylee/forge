use std::path::PathBuf;

use anyhow::Result;
use serde::Serialize;

#[derive(Serialize)]
pub struct File {
    pub path: String,
    pub is_dir: bool,
}
